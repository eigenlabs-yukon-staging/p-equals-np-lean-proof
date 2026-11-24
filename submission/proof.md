# SAT branching on a shortest wide residual clause

`SmallWeakBackdoorShortestWidthSATInP` constructs a reference P
language inside SAT. Given a satisfying assignment and a weak
2-CNF backdoor A, each subset restriction of A either has no
wide clause or has some wide clause of width at most w. The
machine accepts the original CNF if `2^(((w-1).size+1)*A.card)`
fits the prescribed polynomial at the encoded input length.

A verified scanner reads the entire actual residual and retains
a shortest clause of width above two, with ties resolved in input
order. Its output supplies the branch index width. Completeness
follows a satisfying weak backdoor, and soundness holds for
arbitrary code words via the pinned 2-SAT and restriction proofs.

`ShortestWidthBudgetSeparation` exhibits a family in which the
first clause is arbitrarily long and the second clause has three
literals. One literal satisfies both. The shortest-clause budget
is eight. The first-wide sufficient condition fails at that budget
for any satisfying assignment and weak backdoor. Both declarations
and the independent `P_subset_NP` passed the pinned checker.

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
