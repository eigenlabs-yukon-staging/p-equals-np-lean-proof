import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

SCRIPT_DIRECTORY = Path(__file__).resolve().parent
ROOT = SCRIPT_DIRECTORY / "files" if (SCRIPT_DIRECTORY / "files").is_dir() else SCRIPT_DIRECTORY
REVISION = "a9ad395e8fab5537a9017734c14360773f375cd8"
TARGETS = (
    "DisjunctiveHardImage",
    "SparsePruningAlgorithm",
    "SparseHardFrontier",
    "WitnessSearchOfCollapse",
    "CollapseIffWitnessSearch",
    "ShortSeedWitnessSearch",
    "PolynomialWitnessRecovery",
    "PolynomialWitnessSearch",
    "LogWitnessCollapse",
    "P_subset_NP",
    "FiniteWitnessSearch",
    "ConstantWitnessBound",
)


def check(reference, timeout):
    release = subprocess.check_output(
        ["git", "-C", reference, "rev-parse", "HEAD"], text=True, timeout=timeout
    ).strip()
    if release != REVISION:
        raise ValueError(f"Expected reference {REVISION}, got {release}")

    for name in TARGETS:
        module = Path("lean", "PEqualNP", "Outside", f"{name}.lean")
        source = (ROOT / module).read_bytes()
        destination = reference / module
        if destination.exists() and destination.read_bytes() != source:
            raise ValueError(f"Refusing to replace divergent module {module}")
        destination.write_bytes(source)

    results = {}
    for name in TARGETS:
        result = subprocess.run(
            [
                "node", reference / "tools/check-lean.mjs",
                reference / "lean/PEqualNP/Outside" / f"{name}.lean",
                ROOT / "statements" / f"{name}.statement",
                "check",
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
        matches = {
            name: all(sha256((ROOT / path).read_bytes()).hexdigest() == digest
                      for path, digest in target["files"].items())
            for name, target in record.items()
        }
        print(json.dumps({
            "status": "reference_checkout_unavailable",
            "targets": list(TARGETS),
            "kernel_checks_run": 0,
            "recorded_local_checks": {name: target["result"] for name, target in record.items()},
            "recorded_source_hashes_match": matches,
        }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
