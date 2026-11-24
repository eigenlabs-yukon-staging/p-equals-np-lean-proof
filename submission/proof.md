# SAT with a first-wide-residual-clause budget

For each polynomial p, `SmallWeakBackdoorResidualWidthSATInP` builds
a P language contained in reference SAT. Suppose a satisfying
assignment gives a weak 2-CNF backdoor A. For each subset B of A,
consider the first wide clause of the actual residual under the
assignment on B. If every such first clause has width at most w,
the language accepts the original formula whenever
`2^(((w-1).size+1)*A.card)` fits p of the encoded input length.

The machine counts names in only the selected residual clause and
reads the corresponding number of binary index bits plus a truth
bit. This leaves the machine independent of w. The weak-backdoor
hitting argument ensures a search path exists. Each step chooses a
fresh variable from A. Restriction soundness applies to every accepted
code. Completion uses the pinned polynomial-time 2-SAT language.

`ResidualWidthBudgetSeparation` checks a family with arbitrary
original width. A three-literal clause comes first. Both clauses
contain the same positive literal, which satisfies both when set to
true. The adaptive condition holds with budget eight. The maximum
original width grows with the family parameter and its sufficient
condition fails for every candidate backdoor at budget eight.
Both declarations and the independent `P_subset_NP` passed the
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
