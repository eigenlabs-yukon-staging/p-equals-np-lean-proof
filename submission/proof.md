# SAT model extraction from decision on restriction-closed fragments

`RestrictionClosedSATSearch` checks a generic decision-to-search
simulation. For any restriction-closed CNF fragment with a sound and
complete polynomial-time SAT decision predicate on that fragment,
there is a pinned polynomial-time function that extracts a satisfying
assignment for every satisfiable input in the fragment. It returns a
reference-encoded list of positive unit clauses naming the true
variables. All other variable values are false.

The measured machine tries assigning false at each fresh encoded
variable name. If the resulting actual residual is unsatisfiable, the
opposite value preserves a satisfying completion. A proof checks
the invariant at each occurrence, including repeated names and
clause separators. A checked end-of-scan lemma connects the recorded
assignments to a total satisfying assignment. Restriction closure
allows the machine to use the original decision procedure at each
trial.

`RenamableHornSATSearch` instantiates the generic theorem using the
verified renamable-Horn satisfiability decider. `SATIffModelExtraction`
checks an equivalence for general SAT using the reference witness
format and verifier in the reverse direction. It makes no claim that
general SAT lies in P or that an unconditional universal extractor
exists. All three declarations and `P_subset_NP` passed the pinned
checker.

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
