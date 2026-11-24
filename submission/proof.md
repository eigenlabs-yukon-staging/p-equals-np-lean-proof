# Renamable-Horn SAT in the pinned P class

`RenamableHornSATInP` proves that the exact language of encoded
satisfiable CNFs admitting a consistent Horn polarity renaming
belongs to reference P. This is a satisfiability algorithm for a
restricted fragment and does not put general SAT in P.

The decider constructs the checked 2-CNF of polarity constraints.
It rejects a malformed formula or a failed renamability test.
For satisfiable constraints, a measured greedy 2-SAT self-reduction
recovers explicit flip names. Every trial maintains a satisfiable
residual. A verified relabeling scanner then flips exactly the
chosen occurrences, and the checked Horn-SAT routine decides the
relabeled formula. Pure Lean lemmas verify that the result is Horn
and that consistent relabeling preserves satisfiability. The
pinned checker accepted the main theorem, the independent Horn
solver, and `P_subset_NP`.

## Reproduce

Prepare a checkout of brilliant-hq/pequalnp-proofs at
`a9ad395e8fab5537a9017734c14360773f375cd8` with Elan, Node.js and the
Mathlib cache from `lake exe cache get` in its `lean` directory.
Install the submitted proof sources into that checkout with

```sh
python3 submission/check.py --overlay /path/to/pinned/reference
```

The command installs only submitted Outside modules and refuses to
overwrite different source. The split XZ archive also contains the
unchanged upstream proof dependencies. The checker compares the
decoded bytes with the pinned checkout before running. With
`PEQUALNP_REFERENCE_ROOT` set to the absolute reference checkout, run

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The exact statements and recorded checker manifests are supplied.
Hosted Python can check source hashes but does not run Lean.
