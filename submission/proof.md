# SAT with a polynomial budget for long-clause variables

`PEqualNP.Outside.LongClauseSATInP` is about the ordinary reference SAT
encoding. For every fixed polynomial p, it constructs a language in
the reference P contained in SAT. The language agrees with SAT on
CNFs for which 2 to the power of the number of distinct variables
appearing in clauses of length greater than two is at most p(input
length). It may accept some satisfiable inputs outside that promise.

A new scanner collects encoded variable names from every clause
longer than two. A second scanner deduplicates this name list by
first occurrence. Both scans have finite-stack time bounds and exact
semantics over the reference encoding. The output contains all
variables of every long clause. Setting them leaves a 2-CNF, because
every retained long clause becomes empty and the other clauses were
already width at most two. The inherited backdoor solver enumerates
the polynomially many candidate assignments and tests the residual
2-CNF. The public theorem assumes no auxiliary list in the input.
A well-formedness guard rules out every malformed SAT encoding.

The target is a restricted SAT algorithm and a rung 65 submission.
The archive also retains the exact separately checked inclusion
`P_subset_NP`. It makes no claim of an unconditional decision
algorithm for an NP-complete language.

## Reproduce

Check out brilliant-hq/pequalnp-proofs at
`a9ad395e8fab5537a9017734c14360773f375cd8`. Install Elan and Node.js,
and run `lake exe cache get` from the reference checkout's `lean`
directory. Copy this archive's plain `lean/` overlay over the
reference `lean/` directory. The unchanged required reference source
files are also supplied in a split XZ bundle. The checker script
compares the decoded bytes with the pinned checkout before it runs.

With `PEQUALNP_REFERENCE_ROOT` set to the absolute reference checkout
path, run from the challenge checkout:

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The original checker builds and rechecks both theorems against the
independently recorded statements in `statements/`. Its prior
acceptance text, digest, and proof-module source hashes are recorded in
`reference-check.json`. The Python-only hosted experiment compares
the source and statement hashes and reports zero Lean-verified points
when Lean is unavailable.
