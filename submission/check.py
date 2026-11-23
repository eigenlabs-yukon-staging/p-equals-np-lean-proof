import json
import sys

_ = json.load(sys.stdin)
print(json.dumps({
    "proof_ladder_points": 0,
    "detected_targets": [],
    "candidate_lean_files": [],
    "forbidden_tokens": [],
    "reference_checker_results": [],
    "note": "Starter-level lifecycle test submission: no Lean theorem is claimed."
}, sort_keys=True))
