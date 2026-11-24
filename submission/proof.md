# Finite alternating projection under polynomial assignment budgets

`FiniteAlternatingPartialAssignmentProjection` proves a closure
theorem for reference P predicates on canonical CNF inputs. Each
fixed stage chooses existentially or universally among lists of
occurring names and Boolean assignments whose record cost fits a
given polynomial at that stage's residual input length. It then
passes the actual canonical residual to the next stage.

The existential stage uses the exact checked polynomial-budget
projection. A universal stage complements the predicate for the
remaining stages, projects existentially, and complements the
result using the pinned P complement theorem. Induction builds a
P decider for the entire fixed finite sequence. Each stage
recomputes its own budget and name universe on its current CNF.
The statement specifies behavior on canonical encodings.

The number of stages and polynomials are parameters of the
constructed machine. They are not additional input words or an
unbounded quantifier prefix. This is a restricted closure theorem
and does not put general quantified SAT or general SAT in P.
The new declaration and `P_subset_NP` passed the pinned checker.

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
