# One polynomial-time weak-backdoor algorithm across clause widths

`SmallWeakBackdoorVariableWidthSATInP` constructs a reference P language
contained in SAT. If a satisfiable CNF has a weak backdoor a under a
satisfying assignment, its width is at most 2^d, and
`2^((2*d+3)*a.card)` fits the polynomial input budget, the language accepts
its ordinary reference encoding. Both d and a can vary by input.

The algorithm computes each actual residual CNF and then reads the first
wide clause. A self-delimiting record contains a truth bit and a
little-endian binary position. For each position bit, a verified scanner
keeps the even or odd name items. The item list only shrinks. The result
selects precisely the indexed name when it exists. This avoids a
machine whose branching selector is specialized to a fixed width.
The measured path interpreter and bounded enumerator compose with
reference 2-SAT. The ordinary SAT encoding guard applies to all inputs.

`ConstantWeakBackdoorSATInP` obtains an unbounded-width corollary for
each fixed backdoor cardinality k, using the polynomial
`(32 * (input length + 1)^2)^k` for the code budget. Both new targets
and the independent `P_subset_NP` inclusion were accepted by the
pinned checker.

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
