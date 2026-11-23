# Polynomial-time SAT with logarithmically many variables

`PEqualNP.Outside.LogVariableSAT` is checked against the exact reference
classes and SAT encoding. Fix natural numbers c and d. The theorem
constructs L in P contained in SAT and proves that L agrees with SAT on
every encoded CNF with at most `c * log2(encoded length + 1) + d`
distinct occurring variables. The selected language may contain
satisfiable formulas outside the promise. It rejects unsatisfiable or
malformed strings on all inputs.

The compressed witness contains one bit per distinct variable, in
first-occurrence order. The decoder scans the original binary formula.
It retains a list of seen variable codes, consumes an assignment bit on
the first occurrence of a variable, and appends the variable code to the
output on a true bit. The output format is what the pinned SAT verifier
uses. Neither the magnitude of a variable ID nor the number of repeated
occurrences controls the certificate length.

`SatCodeDecoder` implements the decoder as a composition of polynomial-time
string machines. Its transition retains the formula suffix, seen items,
remaining bits, and witness output. The length of the formula suffix is
nonincreasing and bounds each step's growth, even on malformed encodings.
`SatCodeCorrect` proves the loop invariant and the decoded witness
specification for arbitrary CNFs and assignments. The inherited
`EnumeratingSelector` tests the relevant small certificates in length
order using a polynomial clock. The full algorithm guards both decoded
witness length and the pinned SAT verifier answer.

The two targets are `LogVariableSAT` and the independent reference-class
inclusion `P_subset_NP`. The original reference checker accepted both
against statements in `statements/`. For `LogVariableSAT` it rechecked
3,284 project constants and reported only `propext`, `Quot.sound` and
`Classical.choice` as transitive axioms. This is a restricted
polynomial-time decision result and a rung 65 candidate.

## Reproduce the checker

1. Clone brilliant-hq/pequalnp-proofs and check out
   `a9ad395e8fab5537a9017734c14360773f375cd8`.
2. With Elan available, run `lake exe cache get` in that clone's `lean`
   directory. The pin selects Lean 4.36.0 and the committed Mathlib revision.
3. Copy the submitted `lean/` overlay over the prepared clone's `lean/`
   directory. The archive's `upstream-source-*.b64` files also carry the
   exact unchanged reference helper sources as UTF-8 in a split XZ bundle.
   These files decode to the same module bytes as the checkout and need
   no separate installation. `check.py` checks their equality.
4. Export `PEQUALNP_REFERENCE_ROOT` as the absolute path to the prepared
   clone. With Node.js on PATH, run from the challenge checkout:

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The hosted Python experiment reports hash comparisons against the
recorded reference checker manifests. It reports zero Lean-verified points
when the reference toolchain is unavailable. The original checker accepts
the proofs in the prepared Lean environment independent of those comparisons.
