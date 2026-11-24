# Exact projection over a polynomial budget of partial assignments

`BoundedPartialAssignmentProjection` constructs a reference P
decider for any fixed polynomial p and any predicate H in P.
On the pinned pair encoding of a CNF and supplied names A, if
`2^A.length` fits p at the paired input length, membership is exactly
the existence of an assignment to those names whose actual residual
encoding belongs to H. The predicate need not be a satisfiability
test, or even a language of canonical CNF encodings. The queried
residuals themselves always use the canonical encoding.

`SuppliedRenamableHornBackdoorSATInP` instantiates the theorem with
the verified renamable-Horn SAT decider. It accepts exactly when the
original formula has some satisfying assignment whose restriction to
the supplied variables leaves a renamable-Horn residual. The search
needs neither the assignment nor a Horn renaming. Soundness follows
by lifting the residual model to the input formula. It concerns a
budgeted restricted SAT route and does not prove general SAT in P.

Both results and `P_subset_NP` passed the pinned checker.

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
