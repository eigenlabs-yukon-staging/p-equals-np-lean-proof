# Deterministic search over a fixed finite witness collection

The two theorems use the reference verifier predicate
`PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair` and the
reference language class `PEqualNP.Library.P`. The first theorem handles
any fixed list of candidate witnesses. The second takes a fixed natural
number and enumerates every Boolean word of at most that length.

For each candidate, the decider composes the reference identity and
constant-word machines with the reference pair constructor and the
given verifier. It combines the resulting answer bits by a two-state
transducer. Induction on the witness list gives the deterministic
composition. The membership argument is exact for empty collections,
duplicate candidates, and the empty word.

The constant bound is fixed before the machine is chosen. This result
does not give an input-uniform polynomial bound as the witness length
grows, even logarithmically. It does not place general NP in P.

## Reproduce

Prepare a checkout of `brilliant-hq/pequalnp-proofs` at commit
`a9ad395e8fab5537a9017734c14360773f375cd8` and use the pinned Lean
v4.36.0 and Mathlib cache (`lake exe cache get` in the reference
checkout's `lean` directory). Install Node.js for the reference checker.
Run the following from the submission directory, replacing the path
with your prepared checkout.

```sh
python3 check.py --reference /path/to/reference
```

This checks the revision, copies both new modules into the pinned
checkout, refuses to overwrite differing files, and invokes the pinned
exact-statement checker with the included statement files. The standard
JSON experiment reports when the isolated environment has no prepared
Lean checkout.
