"""Run the reference checker when a prepared pinned checkout is available."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

PIN = "a9ad395e8fab5537a9017734c14360773f375cd8"
TARGETS = {
    "P_subset_NP": 50,
    "DecideFromWitnessSearch": 65,
    "CollapseFromWitnessSearch": 65,
}
SOURCE = Path("/snapshot/files")
if not SOURCE.is_dir():
    SOURCE = Path(__file__).resolve().parent


def check(reference, timeout):
    head = subprocess.check_output(
        ["git", "-C", str(reference), "rev-parse", "HEAD"], text=True, timeout=timeout
    ).strip()
    if head != PIN:
        raise ValueError(f"Expected reference commit {PIN}, found {head}")

    overlay = sorted((SOURCE / "lean").rglob("*.lean"))
    for path in overlay:
        dest = reference / "lean" / path.relative_to(SOURCE / "lean")
        if path.read_bytes() != dest.read_bytes():
            raise ValueError(f"Reference checkout lacks the exact submitted overlay: {path.name}")

    results = {}
    for name, points in TARGETS.items():
        target = reference / "lean" / "PEqualNP" / "Outside" / f"{name}.lean"
        statement = SOURCE / "statements" / f"{name}.txt"
        command = ["node", str(reference / "tools" / "check-lean.mjs"),
                   str(target), str(statement), "check"]
        try:
            result = subprocess.run(
                command, cwd=reference, text=True, capture_output=True, timeout=timeout
            )
            verdict = next(
                (line for line in result.stdout.splitlines() if line.startswith("ACCEPTED (check)")),
                None,
            )
            accepted = result.returncode == 0 and verdict is not None
            results[name] = {
                "accepted": accepted,
                "points_if_accepted": points,
                "returncode": result.returncode,
                "verdict": verdict,
                "output_tail": (result.stdout + result.stderr)[-1000:],
            }
        except subprocess.TimeoutExpired:
            results[name] = {"accepted": False, "error": "reference checker timed out"}
    return results


def main():
    inputs = json.load(sys.stdin)
    reference = os.environ.get("PEQUALNP_REFERENCE_ROOT")
    sources = {
        name: (SOURCE / "lean" / "PEqualNP" / "Outside" / f"{name}.lean").is_file()
        and (SOURCE / "statements" / f"{name}.txt").is_file()
        for name in TARGETS
    }
    output = {
        "proof_ladder_points": 0,
        "source_and_statement_present": sources,
        "reference_commit": PIN,
    }
    if inputs.get("reference_commit") != PIN:
        output["status"] = "input did not select the pinned reference"
    elif not reference or not shutil.which("node") or not shutil.which("lake"):
        output["status"] = "Lean was not run. A prepared pinned checkout, Node.js and Lake are required."
    else:
        try:
            results = check(Path(reference).resolve(), inputs["timeout_seconds"])
            output["reference_checker_results"] = results
            output["proof_ladder_points"] = max(
                (item["points_if_accepted"] for item in results.values() if item["accepted"]),
                default=0,
            )
            output["status"] = "reference checker executed"
        except (OSError, ValueError, subprocess.SubprocessError) as exc:
            output["status"] = f"reference checker unavailable: {exc}"
    print(json.dumps(output, sort_keys=True))


if __name__ == "__main__":
    main()
