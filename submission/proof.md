# Bounded witness search and logarithmic witness codes

The target is rung 65. `EqualityIffWitnessSearch` proves the equivalence of
`PEqualNP.Library.P = PEqualNP.Library.NP` and polynomial-time bounded witness
selection for every fixed polynomial-time verifier and bound. The predecessor
gives the search-to-decision direction. The candidate extends that result with
the decision-to-search direction below. Neither side is established
unconditionally.

The search-to-decision direction gives a conditional decision construction for
an arbitrary verifier in the pinned NP definition, then packages that construction
as an implication to the exact inclusion `PEqualNP.Library.NP ⊆ PEqualNP.Library.P`.
The witness-search hypothesis remains open. Rung 50 has the independently checked
exact inclusion `PEqualNP.Library.P ⊆ PEqualNP.Library.NP` from upstream `L010`.

## Polynomial-time decision with logarithmic witness codes

`LogWitnessCodesInP` establishes membership in the reference P when every
positive input has a logarithmic-length code for a valid, bounded witness and
the decoder is polynomial-time. The witness itself may be polynomial in the
input length. The theorem first builds a short-code verifier by composing the
decoder with the original length-guarded verifier. `LogWitnessesInP` is the
special case that tests short witnesses directly.

The enumeration follows the upstream bit-string successor transducer. It
visits strings in order of length and stops changing its candidate once the
guarded verifier accepts. If a valid code has length at most
`c * Nat.log2 (x.length + 1) + d`, its enumeration index is at most the
polynomial `2^(d+1) * (x.length+1)^c`. A finite-stack loop runs for that
polynomial number of steps. Each step increases the packed state by at most
two bits, including on malformed encodings. The same clocked-selector
machinery bounds this loop and the inherited prefix-search loop.

These are restricted tractability results. A general logarithmic-code
guarantee or a polynomial-time decoder with that guarantee is an open
premise here. The inherited P = NP equivalence remains conditional in both
directions.

## Decision-to-search construction

- `PrefixDecideHelpers.extensions_np` shows that prefix extension is in NP.
  On a query encoding an input and a prefix, the witness is the suffix.
  The verifier reconstructs the complete witness and checks its length and
  the supplied relation. The suffix bound follows from the complete witness
  bound and monotonicity of natural polynomial evaluation.
- Under P = NP, the prefix language has a polynomial-time decider.
  `PrefixSelector.selector_of_extensions` runs a finite-stack machine loop
  that keeps the input and the selected prefix. It first checks whether the
  prefix is already a valid witness. Otherwise it asks if appending false
  can extend to a valid witness and chooses true if false cannot.
- The prefix invariant guarantees a valid completion throughout the loop.
  Once a witness is found, later iterations preserve it. There are
  `p.eval x.length` rounds, and each step grows the encoded state by at most
  two bits on all inputs, including malformed states. The reference iteration
  bound therefore supplies the polynomial-time total selector.

## Search-to-decision construction

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
definitions. All imported project proof helpers are included from the Apache-2.0 reference
commit. Upstream modules appear as plain Lean sources or as per-file
base64-encoded gzip source in `upstream-source-*.json` to fit the verifier
snapshot limits. The decoded bytes are checked against the pinned checkout
and the checker manifests. The new Outside proofs are plain Lean. The definitions and checker are supplied by
the pinned reference project.

## Reproduce

Clone `https://github.com/brilliant-hq/pequalnp-proofs` and check out
`a9ad395e8fab5537a9017734c14360773f375cd8`. With Elan, Node.js, and Python 3
available, run `lake exe cache get` from the reference checkout's `lean`
directory. Copy the contents of the submitted `lean/` tree over the reference
checkout's `lean/` tree. This adds the `Outside` sources and leaves
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
reference checker returned exit 0 and `ACCEPTED (check)` for all six
recorded statements. The script reported 65 from those executions. The
hosted Python-only runtime does not reproduce that local Lean verdict.

The observed checker results are recorded in `reference-check.json`.
It records the independent statement and raw transcript digests, the
acceptance text, and the full set of source hashes from the checker
manifests. Source and definition hashes shared by multiple runs are stored
once. The host's comparison checks the submitted module and statement bytes
against that record without executing Lean.

The new equivalence returned `ACCEPTED (check)` after the checker rechecked
2,403 project constants. The axiom set was `Quot.sound`, `propext` and
`Classical.choice`. The hosted experiment separately compares the archive's
proof-module hashes against each transcript manifest, including the decoded
source modules. This comparison does not execute Lean.
