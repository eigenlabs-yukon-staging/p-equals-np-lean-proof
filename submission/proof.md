# Lexicographically least models on restriction-closed SAT fragments

`RestrictionClosedLeastSATModel` checks a polynomial-time model
extractor for any restriction-closed CNF fragment with a polynomial
SAT decider. The same greedy machine also returns the
lexicographically least satisfying assignment when compared in
the input's literal-occurrence order, with false before true.
The output is a reference-encoded list of positive unit clauses
naming the true variables. The theorem is conditional on the
fragment's polynomial-time decision hypothesis.

The new invariant preserves previously selected values and compares
the answer against every satisfying completion that agrees with the
prefix. At a fresh variable a competing model using false witnesses
satisfiability of the false trial. Consequently any first differing
model bit from the computed answer is larger. Repeated variables
preserve the earlier comparison and clause delimiters contribute
no assignment bits.

`RenamableHornLeastSATModel` instantiates the result using the
verified renamable-Horn solver. It is a restricted SAT theorem and
does not establish a general NP-complete target or unconditional
universal search problem in P. Both declarations and `P_subset_NP`
passed the pinned checker.

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
