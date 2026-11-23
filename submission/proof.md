# Polynomial-time SAT with a supplied strong 2-CNF backdoor

`PEqualNP.Outside.TwoSatBackdoorInP` works with the exact reference
`P`, `KSAT 2`, and CNF encoding. A binary input packages a CNF and
a list of variable names. Every accepted such input encodes a
satisfiable formula. If deleting literals whose variables appear on
the list leaves at most two literals per clause and there are only
polynomially many assignments to the list, the computed language
accepts every satisfiable input of that form.

For a candidate bit string, a checked scan selects the variable names
assigned true. A second scan simplifies the original encoding under
that partial assignment. It copies unassigned literals, removes
assigned-false literals, and removes a whole clause when some assigned
literal is true. Its result is the exact reference encoding of the
restricted formula. The reference polynomial-time 2-SAT solver tests
that result. The checked bounded search machine enumerates candidate
bit strings up to a polynomial clock. The width and budget hypotheses
are used for completeness. Soundness holds for every encoded formula
and supplied list, even if the hypotheses fail.

The theorem supplies a restricted SAT algorithm and a component for a
reduction that would find suitably small backdoors. The archive does
not construct such a backdoor for arbitrary CNFs. It also retains the
separately checked exact inclusion `P_subset_NP`.

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
