"""Run the reference checker when a prepared pinned checkout is available."""

import base64
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

PIN = "a9ad395e8fab5537a9017734c14360773f375cd8"
TARGETS = {
    "EqualityIffWitnessSearch": 65,
    "P_subset_NP": 50,
    "DecideFromWitnessSearch": 65,
    "CollapseFromWitnessSearch": 65,
}
SOURCE = Path("/snapshot/files")
if not SOURCE.is_dir():
    SOURCE = Path(__file__).resolve().parent


def sources():
    overlay = {
        path.relative_to(SOURCE / "lean").as_posix(): path.read_bytes()
        for path in (SOURCE / "lean").rglob("*.lean")
    }
    for bundle in sorted(SOURCE.glob("upstream-source-*.json")):
        for name, value in json.loads(bundle.read_text()).items():
            if name in overlay:
                raise ValueError(f"Repeated Lean source: {name}")
            if not name.startswith("PEqualNP/Library/") or ".." in Path(name).parts:
                raise ValueError(f"Unexpected packed module path: {name}")
            overlay[name] = gzip.decompress(base64.b64decode(value, validate=True))
    return overlay


def compare_transcript(overlay):
    hashes = {
        path.removesuffix(".lean").replace("/", "."): hashlib.sha256(data).hexdigest()
        for path, data in overlay.items()
    }
    results = {}
    manifest = None
    for line in (SOURCE / "reference-check.log").read_text().splitlines():
        if line.startswith("MANIFEST "):
            manifest = json.loads(line.removeprefix("MANIFEST "))
        if line.startswith("ACCEPTED (check): ") and manifest is not None:
            target = line.split(";")[0].removeprefix("ACCEPTED (check): ").split(".")[-1]
            imports = {
                item["module"]: item["sha256"] for item in manifest["rests_on"]
            }
            results[target] = {
                "submitted_modules": len(imports),
                "source_hashes_match": all(hashes.get(module) == expected
                                           for module, expected in imports.items()),
            }
            manifest = None
    return results


def check(reference, timeout, overlay):
    head = subprocess.check_output(
        ["git", "-C", str(reference), "rev-parse", "HEAD"], text=True, timeout=timeout
    ).strip()
    if head != PIN:
        raise ValueError(f"Expected reference commit {PIN}, found {head}")

    for name, data in sorted(overlay.items()):
        if (reference / "lean" / name).read_bytes() != data:
            raise ValueError(f"Reference checkout lacks the exact submitted overlay: {name}")

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
    overlay = sources()
    inventory = {
        name: (SOURCE / "lean" / "PEqualNP" / "Outside" / f"{name}.lean").is_file()
        and (SOURCE / "statements" / f"{name}.txt").is_file()
        for name in TARGETS
    }
    output = {
        "proof_ladder_points": 0,
        "source_and_statement_present": inventory,
        "transcript_source_comparison": compare_transcript(overlay),
        "reference_commit": PIN,
    }
    if inputs.get("reference_commit") != PIN:
        output["status"] = "input did not select the pinned reference"
    elif not reference or not shutil.which("node") or not shutil.which("lake"):
        output["status"] = "Lean was not run. A prepared pinned checkout, Node.js and Lake are required."
    else:
        try:
            results = check(Path(reference).resolve(), inputs["timeout_seconds"], overlay)
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
