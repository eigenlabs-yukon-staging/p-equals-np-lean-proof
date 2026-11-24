# SAT with a smaller automatically extracted 2-CNF backdoor

`PEqualNP.Outside.PrefixClauseSATInP` constructs a reference P language
contained in SAT. It accepts every satisfiable reference-encoded CNF
whose extracted variables have at most a fixed polynomial number of
assignments. In each clause the extractor takes the variable names of
all its literal positions except the last two and then deduplicates
across clauses. No extra input is supplied. The resulting language may
accept satisfiable encodings outside the promise.

The binary extractor retains the last two names seen in the current
clause. Each next literal moves the older name to a buffer and advances
the two-name window. At the clause terminator the buffer is emitted,
while the names still in the window are discarded. The growth bound
and finite-stack iteration proof hold for arbitrary input strings.
A correctness theorem identifies the output on the exact reference
CNF encoding. The deduplicated list has the same variable set as that
output. In each clause, deleting all literals on the list can leave
only some of the final two positions. This is the width condition for
the prior backdoor solver. A pinned well-formedness check protects
the soundness claim on all binary inputs.

`PrefixBackdoorBudgetImproves` proves that the new distinct-name count
is always at most the prior long-clause count, with a strict example.
The independent `P_subset_NP` inclusion is retained. The claimed
rung is 65 for the checked restricted SAT construction. None of the
declared theorems places full SAT in P.

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
