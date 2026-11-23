import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

TARGETS = {
    "P_subset_NP": {
        "points": 50,
        "name": "PEqualNP.Outside.P_subset_NP",
        "statement": "PEqualNP.Library.P ⊆ PEqualNP.Library.NP",
    },
    "NP_subset_P": {
        "points": 90,
        "name": "PEqualNP.Outside.NP_subset_P",
        "statement": "PEqualNP.Library.NP ⊆ PEqualNP.Library.P",
    },
    "P_eq_NP": {
        "points": 100,
        "name": "PEqualNP.Outside.P_eq_NP",
        "statement": "PEqualNP.Library.P = PEqualNP.Library.NP",
    },
}
BAD_TOKENS = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
REFERENCE_IMPORTS = ("PEqualNP.Defs", "PEqualNP.Library")

def run(cmd, cwd, timeout):
    try:
        p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
        return {"cmd": cmd, "returncode": p.returncode, "output_tail": p.stdout[-6000:]}
    except FileNotFoundError as exc:
        return {"cmd": cmd, "returncode": 127, "output_tail": str(exc)}
    except subprocess.TimeoutExpired as exc:
        out = (exc.stdout or "") + (exc.stderr or "")
        return {"cmd": cmd, "returncode": 124, "output_tail": out[-6000:]}

def likely_relevant(text):
    needles = ["P_subset_NP", "NP_subset_P", "P_eq_NP", "PEqualNP.Library.P", "PEqualNP.Library.NP", "PolyTimeReducible", "NPComplete", "DecidableInPolyTime"]
    return any(n in text for n in needles)

inp = json.load(sys.stdin)
timeout = int(inp.get("timeout_seconds", 300))
root = Path.cwd()
lean_files = sorted(root.rglob("*.lean"))

candidates = []
for path in lean_files:
    rel = path.relative_to(root).as_posix()
    text = path.read_text(errors="replace")
    if likely_relevant(text):
        candidates.append(rel)

bad_hits = []
for rel in candidates:
    text = (root / rel).read_text(errors="replace")
    for m in BAD_TOKENS.finditer(text):
        bad_hits.append({"file": rel, "token": m.group(1)})

detected = []
for rel in candidates:
    text = (root / rel).read_text(errors="replace")
    for key, target in TARGETS.items():
        if key in text or target["name"] in text or target["statement"] in text:
            detected.append({"target": target["name"], "points": target["points"], "file": rel, "statement_seen": target["statement"] in text})

checker_results = []
checker = root / "tools" / "check-lean.mjs"
if checker.exists() and shutil.which("node") and not bad_hits:
    for target in TARGETS.values():
        target_file = root / "lean" / "PEqualNP" / "Outside" / (target["name"].split(".")[-1] + ".lean")
        if not target_file.exists():
            continue
        with tempfile.NamedTemporaryFile("w", suffix=".lean-statement", delete=False) as f:
            f.write(target["statement"] + "\n")
            stmt_path = f.name
        checker_result = run(["node", str(checker), str(target_file), stmt_path, "check"], root, timeout)
        checker_results.append({"target": target["name"], "points": target["points"], "result": checker_result})
        try:
            os.unlink(stmt_path)
        except OSError:
            pass

accepted_points = [r["points"] for r in checker_results if r["result"]["returncode"] == 0 and "ACCEPTED (check)" in r["result"]["output_tail"]]
proof_ladder_points = max(accepted_points) if accepted_points else 0

result = {
    "proof_ladder_points": proof_ladder_points,
    "detected_targets": detected[:50],
    "candidate_lean_files": candidates[:80],
    "forbidden_tokens": bad_hits[:20],
    "reference_checker_results": checker_results,
    "note": "This harness only provides executable evidence. The reviewer assigns the final ladder score by reading checked Lean source, run logs, and the challenge rubric.",
}
print(json.dumps(result, indent=2, sort_keys=True))
