# From bounded witness search to a polynomial-time decider

The target is rung 65. The candidate gives a conditional decision construction for
an arbitrary verifier in the pinned NP definition, then packages that construction
as an implication to the exact inclusion `PEqualNP.Library.NP ⊆ PEqualNP.Library.P`.
The witness-search hypothesis remains open. Rung 50 has the independently checked
exact inclusion `PEqualNP.Library.P ⊆ PEqualNP.Library.NP` from upstream `L010`.

## Proofs

- `DecideFromWitnessSearch` accepts a relation `R`, witness-length polynomial
  `p`, and polynomial-time witness selector `s`. For a YES input, `s x` must
  meet the verifier and length checks. The decider forms `(x, s x)` using
  `Machines.cpt_pair` and evaluates both tests using `Machines.nf_decider`.
  The latter supplies a polynomial-time witness-length guard on the exact
  tagged-pair encoding. `Machines.cpt_comp` supplies the total polynomial
  running-time bound. For a NO input the selector may return any string.
  Acceptance would exhibit a bounded witness, contradicting the specification.
- `CollapseFromWitnessSearch` applies the first theorem after unpacking the
  witnesses of membership in the pinned NP class. Its premise quantifies over
  each polynomial-time relation and length polynomial, giving a polynomial-time
  selector for each fixed pair. It leaves the existence of those selectors open.
- `P_subset_NP` applies `L010`. Its verifier projects the first component and
  its length bound is zero.

The independent statements in `statements/` only use Mathlib and reference
definitions. All imported project proof helpers are included byte-for-byte from
the Apache-2.0 reference commit. The definitions and checker are supplied by
the pinned reference project.

## Reproduce

Clone `https://github.com/brilliant-hq/pequalnp-proofs` and check out
`a9ad395e8fab5537a9017734c14360773f375cd8`. With Elan, Node.js, and Python 3
available, run `lake exe cache get` from the reference checkout's `lean`
directory. Copy the contents of the submitted `lean/` tree over the reference
checkout's `lean/` tree. This adds the three `Outside` sources and leaves
upstream source bytes unchanged. Set `PEQUALNP_REFERENCE_ROOT` to the absolute
reference checkout path, then from the challenge checkout run

```sh
python3 submission/check.py <<'JSON'
{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}
JSON
```

Each target invokes the original `tools/check-lean.mjs` with the separately
recorded statement. The checker rechecks the theorem's dependencies, axiom
allowlist, and exact statement in the pinned environment. The executable
reports a score of zero when it cannot run Lean. In the hosted Python
experiment, available source files are reported under
`source_and_statement_present` for the reviewer.

## Local reproduction result

On Linux x86-64 with the pinned Lean and Mathlib revisions, the original
reference checker returned exit 0 and `ACCEPTED (check)` for all three
recorded statements. The script reported 65 from those executions. The
hosted Python-only runtime does not reproduce that local Lean verdict.

The raw output of an independent repeat of the three checker invocations is
in `reference-check.log`. Each manifest binds the theorem and helper source
bytes and the reference definitions. The acceptance lines give the
transitive axiom set and the number of constants rechecked by the kernel.
