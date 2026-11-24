import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

SCRIPT_DIRECTORY = Path(__file__).resolve().parent
ROOT = SCRIPT_DIRECTORY / "files" if (SCRIPT_DIRECTORY / "files").is_dir() else SCRIPT_DIRECTORY
REVISION = "a9ad395e8fab5537a9017734c14360773f375cd8"
SUPPORT_MODULES = ('CompressedVariableTruthBoundary', 'FiberCompressionPass', 'OrderedSparseFrontierSolver', 'SparseRepresentativesMachine')
TARGETS = (
    "TruthTableSparseWitnessThreshold",
    "TruthTableSparseWitnessEnumeration",
    "TruthTableSparseNextWitness",
    "LexTruthTableSparseWitness",
    "ShortlexTruthTableSparseWitness",
    "VariableTruthTableSparseWitness",
    "LastEncodedMatch",
    "MeasuredCompressedTruthBoundary",
    "DirectionalTruthTableTrim",
    "AdaptiveTranscriptSparseCollapse",
    "AdaptiveTranscriptCoSparseCollapse",
    "VariableTruthTableSparseCollapse",
    "MeasuredBoundedTruthTableBoundary",
    "BoundedTruthTableBoundary",
    "TruthTableBoundaryTrim",
    "ParameterizedFrontierExpansion",
    "FrontierFilterByParameter",
    "TrimEncodedFrontier",
    "LexicographicWordCompare",
    "ExactWitnessPadding",
    "LexPrefixQueryNP",
    "PolynomialImageMembership",
    "FrontierExpansionMachine",
    "P_subset_NP",
)


def check(reference, timeout):
    release = subprocess.check_output(
        ["git", "-C", reference, "rev-parse", "HEAD"], text=True, timeout=timeout
    ).strip()
    if release != REVISION:
        raise ValueError(f"Expected reference {REVISION}, got {release}")

    subprocess.run(
        ["git", "-C", reference, "diff", "--quiet", "HEAD", "--", "lean", "tools"],
        check=True, timeout=timeout,
    )

    for name in (*SUPPORT_MODULES, *TARGETS):
        module = Path("lean", "PEqualNP", "Outside", f"{name}.lean")
        source = (ROOT / module).read_bytes()
        destination = reference / module
        if destination.exists() and destination.read_bytes() != source:
            raise ValueError(f"Refusing to replace divergent module {module}")
        destination.write_bytes(source)

    targets = json.loads((ROOT / "reference-check.json").read_text(encoding="utf-8"))["targets"]
    results = {}
    with TemporaryDirectory(prefix="yukon-statements-", dir=reference) as scratch:
        for name in TARGETS:
            statement = Path(scratch) / f"{name}.statement"
            statement.write_text(targets[name]["statement"], encoding="utf-8")
            result = subprocess.run(
                [
                    "node", reference / "tools/check-lean.mjs",
                    reference / "lean/PEqualNP/Outside" / f"{name}.lean",
                    statement, "check",
                ],
                cwd=reference,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout,
            )
            results[name] = {
                "returncode": result.returncode,
                "last_line": result.stdout.splitlines()[-1] if result.stdout else "",
            }
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path)
    args = parser.parse_args()
    if args.reference:
        results = check(args.reference.resolve(), 1800)
        print(json.dumps(results, indent=2))
        return int(any(result["returncode"] for result in results.values()))

    request = json.load(sys.stdin)
    if request["reference_commit"] != REVISION:
        raise ValueError("Unsupported reference revision")
    configured = os.environ.get("PEQUALNP_REFERENCE_ROOT")
    if configured:
        print(json.dumps(check(Path(configured).resolve(), request["timeout_seconds"])))
    else:
        record = json.loads((ROOT / "reference-check.json").read_text())
        modules, targets = record["modules"], record["targets"]
        matches = {
            name: (
                sha256(target["statement"].encode("utf-8")).hexdigest() == target["statement_sha256"]
                and all(sha256((ROOT / "lean" / "PEqualNP" / "Outside" / f"{module}.lean").read_bytes())
                        .hexdigest() == modules[module] for module in target["modules"])
            )
            for name, target in targets.items()
        }
        print(json.dumps({
            "status": "reference_checkout_unavailable",
            "targets": list(TARGETS),
            "kernel_checks_run": 0,
            "recorded_local_checks": {name: target["result"] for name, target in targets.items()},
            "recorded_source_hashes_match": matches,
        }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
