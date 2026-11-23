"""Evidence harness for the P = NP Lean proof ladder submission.

What this script can and cannot establish:

* It always runs the static checks below on the submitted files. They need only Python.
* It runs Lean only when a clone of the reference repository, with the pinned toolchain and
  the prebuilt Mathlib, is named by the environment variable PEQUALNP_REFERENCE_ROOT. The
  hosted sandbox has no network, no Lean and a 20 second budget, so there `lean_executed`
  is false and `proof_ladder_points` (the points this run itself verified with Lean) is 0.
  The static checks are supporting context only; they are not a Lean check.

Reproduce the Lean check on a machine with elan, Node.js 20+ and git:

    git clone https://github.com/brilliant-hq/pequalnp-proofs ref
    git -C ref checkout a9ad395e8fab5537a9017734c14360773f375cd8
    (cd ref/lean && lake exe cache get)
    echo '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' \
      | PEQUALNP_REFERENCE_ROOT=$PWD/ref python3 submission/check.py
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REFERENCE_COMMIT = "a9ad395e8fab5537a9017734c14360773f375cd8"

# Files copied unchanged from the reference repository at REFERENCE_COMMIT, with the git blob
# id each has there (`git rev-parse <commit>:<path>`). They are the definitions the statements
# are read against and every helper module the submitted theorems rest on.
REFERENCE_BLOBS = {
    "lean/PEqualNP/Defs/Base.lean": "0ccca47235ea568599d880b39b094e50adb7e21d",
    "lean/PEqualNP/Library/Machines/Run.lean": "960e23b436cca022b12deb24caf0d3b7e37b11d8",
    "lean/PEqualNP/Library/Machines/Compose.lean": "c91178b9d585297cff40a727b392c85805305de2",
    "lean/PEqualNP/Library/Machines/ComposeRun.lean": "16d36d14421a59f1b100e6eb0c61f205fb22ffd6",
    "lean/PEqualNP/Library/Machines/FilterMap.lean": "ae43a3e04b2eaf990e16df51d16e75de94822cfb",
    "lean/PEqualNP/Library/L007.lean": "38d020e3ad39c4837d0e210537c8c7ac05156a9a",
    "lean/PEqualNP/Library/L010.lean": "05cc995beb7c21c3b72d0eeb1b594bd3be6c962b",
    "lean/PEqualNP/Library/L016.lean": "f8e9001bf5fe48dc432c1e087b97f4f7eaae9ef1",
}

# The theorems this submission adds, one per file, each named after its module.
TARGETS = [
    {
        "name": "PEqualNP.Outside.P_subset_NP",
        "file": "lean/PEqualNP/Outside/P_subset_NP.lean",
        "statement": "PEqualNP.Library.P ⊆ PEqualNP.Library.NP",
        "rung": 50,
        "conditional": False,
    },
    {
        "name": "PEqualNP.Outside.Collapse_of_NPHard_mem_P",
        "file": "lean/PEqualNP/Outside/Collapse_of_NPHard_mem_P.lean",
        "statement": "∀ L : Language Bool, PEqualNP.Library.NPHard L → L ∈ PEqualNP.Library.P → "
                     "PEqualNP.Library.NP ⊆ PEqualNP.Library.P",
        "rung": 65,
        "conditional": True,
    },
    {
        "name": "PEqualNP.Outside.Equality_of_NPHard_mem_P",
        "file": "lean/PEqualNP/Outside/Equality_of_NPHard_mem_P.lean",
        "statement": "∀ L : Language Bool, PEqualNP.Library.NPHard L → L ∈ PEqualNP.Library.P → "
                     "PEqualNP.Library.P = PEqualNP.Library.NP",
        "rung": 65,
        "conditional": True,
    },
]

# Rungs this submission does not attempt. Nothing here proves an unconditional NP-to-P result.
NOT_CLAIMED = [80, 90, 100]

BAD_TOKENS = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b")
IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)
DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\b", re.M)


def squash(text):
    return " ".join(text.split())


def blob_id(data):
    return hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()


def find_root():
    snapshot = Path("/snapshot/files")
    return snapshot if snapshot.is_dir() else Path(__file__).resolve().parent


def static_checks(root):
    lean_files = sorted(p.relative_to(root).as_posix() for p in (root / "lean").rglob("*.lean"))
    text = {rel: (root / rel).read_text(encoding="utf-8") for rel in lean_files}

    identical = []
    for rel, expected in REFERENCE_BLOBS.items():
        actual = blob_id((root / rel).read_bytes()) if (root / rel).is_file() else None
        identical.append({"file": rel, "reference_blob": expected, "submitted_blob": actual,
                          "identical": actual == expected})

    unexpected = [rel for rel in lean_files
                  if rel not in REFERENCE_BLOBS and rel not in {t["file"] for t in TARGETS}]

    forbidden = [{"file": rel, "token": m.group(1)}
                 for rel, body in text.items() for m in BAD_TOKENS.finditer(body)]

    targets = []
    for t in TARGETS:
        body = text.get(t["file"])
        entry = {"name": t["name"], "file": t["file"], "statement": t["statement"],
                 "rung": t["rung"], "conditional_on_unproved_hypothesis": t["conditional"],
                 "file_present": body is not None}
        if body is not None:
            flat = squash(body)
            entry["declares_exact_statement"] = (
                "theorem " + t["name"] + " : " + squash(t["statement"]) + " :=") in flat
            # One declaration, the theorem itself: nothing in the file can redefine P, NP,
            # languages, reductions or anything else the statement speaks of.
            entry["declarations_in_file"] = len(DECL.findall(body))
            entry["imports"] = IMPORT.findall(body)
            entry["imports_only_submitted_reference_modules"] = all(
                ("lean/" + m.replace(".", "/") + ".lean") in REFERENCE_BLOBS for m in entry["imports"])
        targets.append(entry)

    # Every project import must be a submitted file, except the definitions root itself, which
    # the reference tree supplies (it is 39 files; the statements here use Defs/Base.lean only).
    missing = sorted({m for body in text.values() for m in IMPORT.findall(body)
                      if m.startswith("PEqualNP") and m != "PEqualNP.Defs"
                      and ("lean/" + m.replace(".", "/") + ".lean") not in text})

    ok = (all(i["identical"] for i in identical) and not unexpected and not forbidden and not missing
          and all(t["file_present"] and t["declares_exact_statement"] and t["declarations_in_file"] == 1
                  and t["imports_only_submitted_reference_modules"] for t in targets))
    return {"passed": ok, "lean_files": lean_files, "reference_identical_files": identical,
            "lean_files_outside_the_declared_set": unexpected, "forbidden_tokens": forbidden,
            "unresolved_project_imports": missing,
            "imports_supplied_by_reference_tree": ["PEqualNP.Defs"], "targets": targets}


def run(cmd, cwd, timeout):
    try:
        p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=timeout)
        return p.returncode, p.stdout
    except FileNotFoundError as exc:
        return 127, str(exc)
    except subprocess.TimeoutExpired as exc:
        return 124, exc.stdout if isinstance(exc.stdout, str) else ""


def lean_checks(root, reference, timeout):
    """Overlay the submitted files on the reference clone and run the reference checker."""
    reference = Path(reference).resolve()
    checker = reference / "tools" / "check-lean.mjs"
    if not checker.is_file() or not shutil.which("node") or not shutil.which("git"):
        return {"lean_executed": False, "reason": "reference checker, node or git not found"}, []
    code, head = run(["git", "-C", str(reference), "rev-parse", "HEAD"], None, 60)
    if code != 0 or head.strip() != REFERENCE_COMMIT:
        return {"lean_executed": False,
                "reason": "reference clone is not at " + REFERENCE_COMMIT}, []
    # Reference files are never replaced: a submitted copy must equal the file already there.
    for rel in REFERENCE_BLOBS:
        if (reference / rel).read_bytes() != (root / rel).read_bytes():
            return {"lean_executed": False, "reason": rel + " differs from the reference clone"}, []
    for t in TARGETS:
        (reference / t["file"]).write_bytes((root / t["file"]).read_bytes())
    results = []
    for t in TARGETS:
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False, encoding="utf-8") as f:
            f.write(t["statement"] + "\n")
            statement = f.name
        try:
            code, output = run(["node", str(checker), str(reference / t["file"]), statement, "check"],
                               str(reference), timeout)
        finally:
            os.unlink(statement)
        lines = output.strip().splitlines()
        results.append({"name": t["name"], "rung": t["rung"], "returncode": code,
                        "accepted": code == 0 and bool(lines) and lines[-1].startswith("ACCEPTED (check)"),
                        "output_tail": "\n".join(lines[-12:])[-6000:]})
    return {"lean_executed": True, "reference_root_commit": head.strip()}, results


def main():
    raw = "" if sys.stdin.isatty() else sys.stdin.read()
    inp = json.loads(raw) if raw.strip() else {}
    timeout = int(inp.get("timeout_seconds", 300))
    root = find_root()
    static = static_checks(root)

    reference = os.environ.get("PEQUALNP_REFERENCE_ROOT")
    if inp.get("reference_commit", REFERENCE_COMMIT) != REFERENCE_COMMIT:
        status, checker_results = {"lean_executed": False,
                                   "reason": "this submission is pinned to " + REFERENCE_COMMIT}, []
    elif reference and static["passed"]:
        status, checker_results = lean_checks(root, reference, timeout)
    else:
        status, checker_results = {
            "lean_executed": False,
            "reason": "no reference clone and Lean toolchain in this environment "
                      "(set PEQUALNP_REFERENCE_ROOT to run the reference checker)"}, []

    accepted = [r["rung"] for r in checker_results if r["accepted"]]
    all_accepted = bool(checker_results) and all(r["accepted"] for r in checker_results)
    result = {
        "proof_ladder_points": (max(accepted) if all_accepted else 0),
        "proof_ladder_points_meaning": "highest rung whose theorems the reference checker accepted "
                                       "in THIS run; 0 when Lean did not run here",
        "attempted_rung": 65,
        "rungs_not_claimed": NOT_CLAIMED,
        "reference_commit": REFERENCE_COMMIT,
        "static_checks": static,
        "reference_checker_results": checker_results,
        "note": "Static checks are supporting context, not a Lean check. The score is the "
                "reviewer's, from the Lean source and reproducible evidence.",
    }
    result.update(status)
    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))


main()
