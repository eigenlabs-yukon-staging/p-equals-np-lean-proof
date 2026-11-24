# An optimal-comparator witness characterization of P = NP

`OptimalComparatorWitnessSearch` proves an exact equivalence.
Under P = NP, every fixed polynomial-time bounded verifier and
polynomial-time strict transitive comparator admit a
polynomial-time function returning an undominated feasible
witness whenever one exists. The comparator may be partial
and may depend on the input. It need not be given by an explicit
numerical or word-valued objective. Conversely the general
optimization principle implies P = NP. Neither side is proved
unconditionally.

A better feasible witness is a polynomial-length NP certificate
against optimality. Under the equality hypothesis, the checker
for absence of such an improvement is polynomial time by
complementation. Finite abstract minimality ensures at least one
feasible optimum exists. The checked search-to-decision
equivalence then extracts it. The proof does not enumerate the
exponential feasible set at runtime.

The pinned checker accepted the equivalence and independent
`P_subset_NP` declaration.

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
