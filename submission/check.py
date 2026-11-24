"""Run the reference checker when a prepared pinned checkout is available."""

import base64
import hashlib
import json
import lzma
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys

PIN = "a9ad395e8fab5537a9017734c14360773f375cd8"
TARGETS = {"AffineIsolatedNPQueryVerifier": 65, "P_subset_NP": 50}
SOURCE = Path("/snapshot/files")
if not SOURCE.is_dir():
    SOURCE = Path(__file__).resolve().parent


def sources():
    overlay = {
        path.relative_to(SOURCE / "lean").as_posix(): path.read_bytes()
        for path in (SOURCE / "lean").rglob("*.lean")
    }
    packed = b"".join(
        bundle.read_bytes().strip() for bundle in sorted(SOURCE.glob("upstream-source-*.b64"))
    )
    document = lzma.decompress(base64.b64decode(packed, validate=True), memlimit=96 * 1024 * 1024)
    for name, text in json.loads(document).items():
        if name in overlay:
            raise ValueError(f"Repeated Lean source: {name}")
        if not re.fullmatch(
            r"PEqualNP/(?:Library|MetaComplexity|Outside)/(?:[A-Za-z][A-Za-z0-9_]*/)*"
            r"[A-Za-z][A-Za-z0-9_]*\.lean", name
        ):
            raise ValueError(f"Unexpected packed module path: {name}")
        overlay[name] = text.encode("utf-8")
    return overlay


def compare_transcript(overlay):
    hashes = {
        path.removesuffix(".lean").replace("/", "."): hashlib.sha256(data).hexdigest()
        for path, data in overlay.items()
    }
    evidence = json.loads((SOURCE / "reference-check.json").read_text())
    expected_hashes = evidence["module_sha256"]
    results = {}
    for target, entry in evidence["targets"].items():
        modules = entry["modules"]
        statement = SOURCE / "statements" / f"{target}.txt"
        results[target] = {
            "recorded_verdict": entry["verdict"],
            "submitted_modules": len(modules),
            "source_hashes_match": bool(modules) and all(
                hashes.get(module) == expected_hashes[module] for module in modules
            ),
            "statement_hash_matches": hashlib.sha256(statement.read_bytes()).hexdigest()
            == entry["statement_sha256"],
        }
    return results


def require_pinned_reference(reference):
    head = subprocess.check_output(
        ["git", "-C", str(reference), "rev-parse", "HEAD"], text=True, timeout=30
    ).strip()
    if head != PIN:
        raise ValueError(f"Expected reference commit {PIN}, found {head}")

def install_overlay(reference, overlay):
    require_pinned_reference(reference)
    lean = (reference / "lean").resolve()
    writes = []
    for name, data in sorted(overlay.items()):
        if not name.startswith("PEqualNP/Outside/"):
            continue
        dest = lean / name
        if dest.resolve() != dest or not dest.is_relative_to(lean):
            raise ValueError(f"Unsafe overlay path: {name}")
        if dest.exists():
            if dest.read_bytes() != data:
                raise ValueError(f"Existing source differs; use a clean reference clone: {name}")
        else:
            writes.append((dest, data))
    for dest, data in writes:
        dest.parent.mkdir(parents=True, exist_ok=True)
        with dest.open("xb") as stream:
            stream.write(data)
    print(f"Installed {len(writes)} submitted Outside modules")


def check(reference, timeout, overlay):
    require_pinned_reference(reference)
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
    if len(sys.argv) == 3 and sys.argv[1] == "--overlay":
        install_overlay(Path(sys.argv[2]).resolve(), sources())
    elif len(sys.argv) == 1:
        main()
    else:
        raise SystemExit("Usage: check.py [--overlay PINNED_REFERENCE]")
