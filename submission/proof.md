# A checked polynomial-budget search for strong Horn backdoors

`SmallStrongHornBackdoorSATInP` proves that for each polynomial p
a single reference P language inside SAT decides CNF satisfiability
whenever the input admits a deletion-to-Horn backdoor A and
`4^A.card ≤ p.eval (encodeCNF φ).length`. Deletion-to-Horn means
that removing all occurrences of the variables in A leaves each
clause with at most one positive occurrence. There is no clause-width
cap and no requirement to supply A to the machine.

The obstruction scanner skips negative or already selected literals
and returns the first pair of unchecked positive occurrences in a
single original clause. Any deletion backdoor extending the current
selected subset must contain one of the pair's variables. One branch
bit selects the name and another its truth value. A checked
polytime iterator follows these steps and tests the actual residual
using the Horn solver. Completeness uses a satisfying full assignment
and at most two bits per new backdoor variable. The Horn check and
restriction proof give soundness even on arbitrary code words.

The checked result is a restricted SAT route for the stated structural
and polynomial-budget promise. It does not establish a general
NP-complete target in P. `HornSATInP` and `P_subset_NP` were also
accepted by the pinned checker.

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
