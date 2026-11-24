# A shortest-then-lexicographic witness characterization of P = NP

`ShortestLexWitnessSearch` proves an equivalence. If P equals NP,
then every pinned polynomial-time decidable verifier relation with
a polynomial witness-length bound admits a pinned polynomial-time
extractor of the shortest witness, with lexicographic tie-breaking.
Conversely, such a family of extractors implies the collapse.
The proof does not establish either side unconditionally.

The checked selector uses exact prefix-extension decisions and
chooses the false branch before the true branch, stopping at a
passing prefix. A new invariant proves that this selects the
lexicographically least accepted string. Adding a leading unary
witness-length field and a delimiter makes lexicographic order
prefer shorter original witnesses before comparing their bits.
The transformed verifier checks the exact coding and original
relation in the reference machine model.

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
