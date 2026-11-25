"""Replay exact checks on a separately prepared, pinned reference checkout."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

REFERENCE = "a9ad395e8fab5537a9017734c14360773f375cd8"
TARGETS = (
    "P_subset_NP",
    "MeasuredFirstClause",
    "HornClosureCompleteness",
    "MeasuredPositiveLiteral",
    "MeasuredHornSweep",
    "MeasuredHornSAT",
    "MeasuredHornGuard",
    "ExactHornSAT",
)
OVERLAY = Path("lean/PEqualNP/Outside")
SNAPSHOT = Path("/snapshot/files")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def identity(root, statements):
    return {
        name: {
            "source_sha256": digest(root / OVERLAY / f"{name}.lean"),
            "statement_sha256": hashlib.sha256(statements[name].encode("utf-8")).hexdigest(),
        }
        for name in TARGETS
    }


def replay(reference, root, statements_dir, timeout):
    head = subprocess.check_output(
        ["git", "-C", str(reference), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != REFERENCE:
        raise ValueError(f"Reference HEAD is {head}, expected {REFERENCE}")
    for name in TARGETS:
        rel = OVERLAY / f"{name}.lean"
        dest = reference / rel
        source = (root / rel).read_bytes()
        if dest.exists():
            if dest.read_bytes() != source:
                raise ValueError(f"Overlay conflicts with {rel}")
        else:
            dest.parent.mkdir(parents=True, exist_ok=True)
            with dest.open("xb") as out:
                out.write(source)
    results = {}
    for name in TARGETS:
        command = [
            "node", "tools/check-lean.mjs",
            str(OVERLAY / f"{name}.lean"),
            str(statements_dir / f"{name}.txt"), "check",
        ]
        try:
            run = subprocess.run(
                command, cwd=reference, timeout=timeout, check=False,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
        except subprocess.TimeoutExpired:
            results[name] = {"accepted": False, "error": "checker timeout"}
            continue
        target = f"PEqualNP.Outside.{name}"
        prefix = f"ACCEPTED (check): {target};"
        wanted = [line for line in run.stdout.splitlines() if line.startswith(prefix)]
        accepted = run.returncode == 0 and bool(wanted)
        result = {"accepted": accepted, "returncode": run.returncode}
        if accepted:
            result["verdict"] = wanted[-1].split(" constants of ", 1)[0] + " constants"
            raw_manifest = next(line[9:] for line in run.stdout.splitlines() if line.startswith("MANIFEST "))
            result["manifest"] = json.loads(raw_manifest)
        else:
            result["output_tail"] = run.stdout[-2000:]
        results[name] = result
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    root = SNAPSHOT if SNAPSHOT.is_dir() else Path(__file__).resolve().parent
    statements = json.loads((root / "statements.json").read_text(encoding="utf-8"))
    files = identity(root, statements)
    if args.reference is None:
        request = json.load(sys.stdin)
        if request["reference_commit"] != REFERENCE:
            raise ValueError("Experiment requests a different reference revision")
        report = json.loads((root / "replay.json").read_text())
        compact = {
            name: item["verdict"] for name, item in report["checks"].items()
            if item["accepted"]
        }
        matched = report["files"] == files and report["reference_commit"] == REFERENCE
        print(json.dumps({
            "mode": "archive-identity",
            "archive_matches_recorded_inputs": matched,
            "kernel_checks_executed": 0,
            "recorded_local_verdicts": compact,
            "files": files,
        }))
        return 0 if matched else 1

    reference = args.reference.resolve()
    work = reference / "lean" / ".lake"
    work.mkdir(exist_ok=True)
    with TemporaryDirectory(prefix="exact-statements-", dir=work) as directory:
        statements_dir = Path(directory)
        for name in TARGETS:
            (statements_dir / f"{name}.txt").write_bytes(statements[name].encode("utf-8"))
        checks = replay(reference, root, statements_dir, args.timeout)
    print(json.dumps({
        "reference_commit": REFERENCE,
        "files": files,
        "checks": checks,
    }, indent=2, sort_keys=True))
    return 0 if all(result["accepted"] for result in checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
