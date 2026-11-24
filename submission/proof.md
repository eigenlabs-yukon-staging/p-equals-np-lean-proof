# SAT with an exact branch-path budget

For each polynomial p, `SmallWeakBackdoorPathBudgetSATInP` produces
a reference P language contained in SAT. A certificate states a
satisfying assignment and an ordered list of actual first-wide
residual clauses and the literals chosen in them. It terminates
with an actual 2-CNF residual. Each visit to a clause of length n
costs `(n-1).size+1` bits. The formula is accepted if two to the
power of the sum of visit costs fits p at its encoded input length.

The pinned machine reads its index width from the clause it
actually visits. The new proof follows an external path witness one
visit at a time, encodes the index and truth value in exactly the
stated number of bits, and pads the iteration count by fixed
transitions after reaching the 2-CNF. The search uses the
checked sum of local costs, independent of the widths on other
paths or the worst width among backdoor-subset restrictions.

`WeakBackdoorPathBudgetSeparation` proves a family with a six-bit
path and residuals of unbounded width along a different path.
Budget 64 suffices under the new condition. Every satisfying weak
backdoor must contain both distinguished variables, and the
restriction to just the second variable exposes the long clause.
The predecessor's uniform width condition cannot certify this
family at the same budget. Both declarations and the independent
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
