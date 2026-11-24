# Unassisted fixed-cardinality projection over CNF restrictions

`FixedSizePartialAssignmentProjection` proves exact closure for
each fixed k under existential selection of at most k occurring
variable names and Boolean values. The actual residual is tested
by any specified language H in reference P. The input is only the
original CNF encoding. A machine checks and deduplicates its names,
then decodes binary indices and values for the selected names.
A polynomial code budget follows from the number of distinct
names being bounded by the input length. The machine rejects
malformed CNF encodings.

`FixedSizeWeakRenamableHornBackdoorSATInP` instantiates this with
the checked renamable-Horn SAT decider. It decides the exact
language of formulas admitting a genuine satisfying assignment
and a weak backdoor of size at most k that yields a
renamable-Horn residual. No set of names or value hints are
given to the machine. This is a restricted SAT theorem and
does not put general SAT in P. Both new declarations and
`P_subset_NP` passed the pinned checker.

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
