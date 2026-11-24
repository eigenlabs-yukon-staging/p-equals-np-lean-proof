# SAT given existence of a small strong 2-CNF backdoor

`PEqualNP.Outside.SmallStrongBackdoorSATInP` constructs a language in the
reference P contained in SAT. For each fixed polynomial p, it is complete
on encoded CNFs admitting a finite set a such that deleting literals on
a leaves at most two literals in each clause and 8^|a| is bounded by
p(input length). The input supplies only the original CNF encoding.

The new scanner finds the first three unassigned literal positions in
the first clause with three such positions. Any promised deletion set
extending the choices so far must contain at least one of their names.
A three-bit word chooses one of those names and its Boolean value. The
verified path machine consumes such words and records the selected
variables and the subset set true. Once no obstruction remains it
keeps the state fixed. The remaining-name count in an existential
backdoor decreases at each correct branch. The proof constructs a
successful code of at most three bits per variable in the backdoor.

The inherited shortlex selector and 2-SAT machine supply a
polynomial-time decision procedure on the promise. The scanner,
path evaluation, and encoded partial assignment are proved polynomial
time on arbitrary input strings, including malformed packed states.
Acceptance of a genuine code implies satisfiability of the original
formula, and a well-formedness guard rejects malformed CNF input.
No unconditional SAT-in-P or NP-completeness claim is made. The
independent exact `P_subset_NP` inclusion is supplied as well.

## Reproduce

Check out brilliant-hq/pequalnp-proofs at
`a9ad395e8fab5537a9017734c14360773f375cd8`. With Elan and Node.js
available, run `lake exe cache get` in the pinned clone's `lean`
directory. Copy the submitted plain `lean/` tree into the clone's
`lean/` directory. The archive also includes the unchanged source
dependencies in a split XZ bundle, whose decoded bytes are compared
against the reference checkout by the experiment.

Set `PEQUALNP_REFERENCE_ROOT` to the absolute clone path, then run:

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

The original checker accepted each independently recorded statement.
`reference-check.json` records checker results, transcript digests,
source hashes, and independent statement hashes. In the Python-only
hosted experiment, source and statement integrity are checked and
Lean-verified points remain zero because Lean is unavailable.
