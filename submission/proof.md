# SAT with an input-derived weak-backdoor path budget

`SmallWeakBackdoorWidthBudgetSATInP` constructs a P language inside
the reference SAT language for each polynomial budget. It accepts a
satisfiable formula with a satisfying weak 2-CNF backdoor of size a
whenever 2 to the power ((d + 1) * a) fits that budget, with d the
binary size of the original maximum clause width minus one.

A verified scan computes maximum width as a unary value, then a
verified halving loop gives d. At each step the interpreter finds the
first wide clause of the actual residual, reads d bits to select a
literal position and consumes one truth bit. Soundness follows from
reference 2-SAT and lifting residual assignments. Completeness follows
by following the satisfying assignment and choosing a fresh backdoor
variable from each wide residual clause.

`ConstantWeakBackdoorTightSATInP` gives a polynomial budget of
`(4 * (input length + 1))^k` for each fixed backdoor bound k, with
arbitrary clause widths. Both new theorems and the separate
`P_subset_NP` passed the pinned checker.

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
