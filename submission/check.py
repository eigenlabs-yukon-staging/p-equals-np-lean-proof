import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REVISION = "a9ad395e8fab5537a9017734c14360773f375cd8"
TARGETS = ("FiniteWitnessSearch", "ConstantWitnessBound")


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
        print(json.dumps({
            "status": "reference_checkout_unavailable",
            "targets": list(TARGETS),
            "kernel_checks_run": 0,
        }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
