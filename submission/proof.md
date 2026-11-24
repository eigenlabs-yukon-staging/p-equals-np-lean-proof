# A word-cost optimization characterization of P = NP

`OptimalCostWitnessSearchAutoBound` proves an equivalence between
P = NP and polynomial-time bounded-verifier witness extraction with
an arbitrary fixed polynomial-time word-valued cost. The returned
witness minimizes cost length and then cost bits in lexicographic
order. The statement requires no separately supplied polynomial
bound on cost length. The proof obtains one from the reference
polynomial-time output-length lemma and the witness bound.

The checked transformation pairs the cost with the original witness.
The unary length field and the cost prefix cause a least encoded
word to have a least cost, irrespective of the witness payload.
The new verifier recomputes cost and checks the exact encoding,
feasibility, and witness bound. The earlier least-prefix selector
finds the least such encoded witness under P = NP. The converse
uses the constant empty cost and the checked search-to-decision
argument. Neither side is established unconditionally.

Both the explicit-bound and automatic-bound equivalences and
the independent `P_subset_NP` passed the pinned checker.

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
