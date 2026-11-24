# Horn-SAT in the pinned P class

`HornSATInP` proves the exact language of encoded satisfiable Horn
formulas is in reference P. A Horn clause has at most one positive
literal occurrence. The proof uses the ordinary reference encoding
and the actual Turing-machine polynomial-time predicate.

A measured iterator finds a positive unit in the actual residual
and sets its variable true, retaining an encoded list of chosen
names. The scan returns a fresh variable from the original CNF
whenever it moves. A finite set of original variables bounds the
number of nontrivial steps by the input length. All satisfying
assignments agree with the values propagated. When no positive
unit remains, the final residual has a satisfying all-false
assignment exactly when it contains no all-positive clause,
including an empty one. This final check establishes soundness
on every well-formed CNF and completeness on Horn CNFs.

A separate checked guard rejects formulas containing a clause
with two positive occurrences. The encoding guard covers malformed
words and the desired language has no promise on its inputs.
`HornSATSublanguageInP` records the broader sound sublanguage before
applying the Horn guard. Both and `P_subset_NP` passed the pinned
checker.

## Scope

Horn-SAT is a restricted SAT language. This proves a polynomial-time
decider only for the Horn restriction and does not establish any
general NP-complete target or universal verifier/search problem in P.
It supplies a reusable checked subroutine for routes that reduce to
Horn residuals. Its candidate ladder rung is 65.

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
