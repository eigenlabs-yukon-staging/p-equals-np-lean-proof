# Exact SAT-residual projection under a polynomial bit budget

`PolynomialBudgetPartialAssignmentProjection` constructs a P
language for each polynomial p and each residual predicate H in P.
An input CNF has m distinct variable names. An eligible witness
chooses a list of occurring names A and Boolean values subject to
`2^(((m-1).size+1)*A.length) ≤ p.eval (encodeCNF φ).length`.
Acceptance is equivalent to existence of an eligible choice whose
actual residual encoding is in H. No names or backdoor bound are
supplied as input.

The checked interpreter truncates each code to the binary size
of its budget minus one, consumes only complete records, and
separately rejects budget zero. A conserved record cost proves
the exact exponent bound for every accepting code. A complete
semantic witness has an exact record encoding and is found by
the polynomial rank enumerator. The well-formedness test rejects
malformed input.

The checked renamable-Horn specialization applies the generic
language construction to a verified residual SAT solver. It decides
the exact restricted language under the stated cost and does not
put general SAT in P. Both new declarations and `P_subset_NP` passed
the pinned checker.

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
