# Recognizing Horn renamability in the pinned P class

`RenamableHornReducesToTwoSAT` proves that the exact language of
CNFs admitting a global polarity flip to Horn is Karp reducible
to reference 2-SAT and belongs to reference P. For each pair of
literal positions in a clause, the compiler emits a two-literal
clause requiring at least one position to turn negative after the
chosen renaming. This permits duplicated literals and empty clauses
and uses the ordinary pinned list and bit encodings.

The compiler scans two suffixes within the current clause. It
emits each ordered-position pair once and never crosses a
clause delimiter. A measured polynomial-time loop implements the
scan, and a proof that the required step count fits a quadratic
clock connects the machine to the pair-formula specification.
A well-formedness guard sends malformed words to a fixed unsatisfiable
2-CNF.

This recognition reduction provides a reusable bridge toward
renamable-Horn SAT. It recognizes whether a renaming exists.
It does not decide satisfiability of the original formula or
solve a general NP-complete target. The pinned checker accepted
the reduction theorem and independent `P_subset_NP` inclusion.

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
