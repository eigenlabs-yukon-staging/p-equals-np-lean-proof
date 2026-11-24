# Minimum-cardinality certificates for budgeted CNF projection

`LeastBudgetedPartialAssignment` proves a polynomial-time search
function for every fixed polynomial p and residual predicate H in P.
When some budget-eligible selection of names and values produces
an H-member residual, it outputs such a selection of minimum
cardinality. The output encodes the selected names and their true
names as canonical unit-clause lists using the reference pair
format. The selected list contains no duplicates.

The checked rank enumerator stops at the first passing word.
Every semantic witness has a branch code of exactly the per-name
record cost times its selected-list length. The rank order is
monotone by word length. The interpreter can consume no more
records than fit in the selected word, so its returned list
cannot be longer than any passing semantic witness. Removing
duplicate names would preserve the same residual and lower the
cost, so the minimum list is duplicate-free.

This is a polynomial-budget search theorem and does not establish
an unrestricted universal witness extractor. Both this declaration
and `P_subset_NP` passed the pinned checker.

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
