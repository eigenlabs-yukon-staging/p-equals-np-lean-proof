# Exact assignment-budget SAT and a collapse criterion

For every fixed polynomial p with natural coefficients,
`VariableBudgetSATInP` proves membership in the exact reference P for the
language of encoded satisfiable CNFs that have at most p(input length)
assignments to their distinct occurring variables. The number of possible
assignments is exactly 2 to the power of the number of distinct variables.
In contrast to a promise decider, this language rejects satisfiable
encodings outside the budget as well as all unsatisfiable and malformed
inputs.

The bit-string decoder inherited from the prior candidate uses one bit
per first occurrence. The strengthened correctness lemma gives exactly
one bit per distinct variable and bounds the decoded witness length by
the original input length. Bounded enumeration needs at most twice the
polynomial assignment budget, even though it includes shorter strings.

The new deterministic budget guard runs the same scanner on an empty
certificate and keeps its list of distinct names. It starts with a
unary string of length p(input length) and halves it once per distinct
name. The remaining length is the original budget divided by
2^(number of names), rounded down. Nonemptiness is therefore equivalent
to the required inequality. The iteration is bounded by the byte
length of the name list. The reference finite-stack time bound applies,
including on arbitrary malformed internal states.

`CollapseIffBudgetedSATReduction` proves P = NP if and only if the exact
SAT language admits a reference polynomial-time many-one reduction into
one of the budgeted languages. A reduction gives SAT in P by closure
under reductions and then P = NP by the pinned Cook–Levin theorem.
In the reverse direction SAT in P permits a reduction into the budget-1
language by emitting a constant yes or no example. The theorem leaves the
existence of an unconditional reduction open. The archive retains the
independent exact `P_subset_NP` proof.

## Reproduce

Clone brilliant-hq/pequalnp-proofs at
`a9ad395e8fab5537a9017734c14360773f375cd8`, and use Elan to select the
reference toolchain. Run `lake exe cache get` from its `lean` directory.
Copy the submitted `lean/` overlay over the reference `lean/` directory.
The split source archive also contains the unchanged upstream module bytes.
The script compares both sets of files with the prepared reference checkout.
With Node.js on PATH and `PEQUALNP_REFERENCE_ROOT` set to the absolute
reference clone path, run

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The original checker reads each independent recorded statement against
Mathlib and the pinned definitions and rechecks the proof's dependencies
and transitive axioms. The exact local results and source hashes are in
`reference-check.json`. In the hosted Python-only experiment the script
compares hashes and reports zero Lean-verified points because Lean is not
available there.
