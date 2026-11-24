# Complexity of verifying that no better bounded witness exists

`OptimalWitnessCheckingInCoNP` proves a coNP upper bound for checking
that a candidate is feasible and no better bounded candidate exists.
The relation and comparator are arbitrary fixed reference
polynomial-time predicates.

`OptimalWitnessCheckingCoNPComplete` constructs a checked
coNP-complete case. A one-bit dummy is always feasible, and any
tagged reference SAT witness beats it. Consequently the dummy is
optimal exactly when the original word is outside SAT. The
comparator is irreflexive and transitive. Pinned SAT completeness
and a verified pairing map supply the lower bound.

`OptimalWitnessCheckingIffCollapse` checks that universal
polynomial-time optimality verification is equivalent to P = NP.
It does not give an unconditional polynomial-time solution for
general SAT, optimality verification, or a universal search problem.
All new statements and `P_subset_NP` passed the pinned checker.

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
unchanged upstream proof dependencies. The archive stores its
first segment in base64 and its tail as fixed-width decimal
blocks with a recorded byte length. The checker reconstructs
and verifies the exact bytes. The checker compares the
decoded bytes with the pinned checkout before running. With
`PEQUALNP_REFERENCE_ROOT` set to the absolute reference checkout, run

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The exact statements and recorded checker manifests are supplied.
Hosted Python can check source hashes but does not run Lean.
