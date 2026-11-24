# Structure of hard languages and the pinned equality

`SparseCoHardImpliesCollapse` constructs a pinned deterministic polynomial-time
normal-form verifier search decider under cumulative sparse coNP-hardness.
`ConjunctiveCoHardImage` and `CoSparsePruningMachine` give its reduction and measured
frontier step. The step can certify a positive answer when there are too many
distinct images for all candidates to reject. `CollapseIffSparseCoHard` adds the
exact-length converse.

`SelectiveHardImpliesCollapse` uses a polynomial-time selector for an NP-hard
language to guide witness-prefix search. `CollapseIffSelectiveHard` proves the
corresponding equivalence. These theorems require the respective structural
hardness premises and make no unconditional collapse claim.

## Exact witness production with an input-supplied search budget

`UnaryBudgetWitnessRecovery` returns the first accepted witness in the reference
short-word-first enumeration up to the supplied clock word length. It returns the empty
word exactly on failure within the range. The clock is measured in actual input symbols.
`UnaryPaddedSearchForNP` specializes the result to each normal-form NP verifier and proves
complete coverage when the supplied padding is sufficiently long. The required padding
can be exponential in the original input length.

## Sparse NP-hardness and the pinned class equality

`SparseHardImpliesCollapse` proves the pinned equality P = NP under the existence of
an NP-hard target whose accepted words of length up to n have polynomially bounded
cardinality. The machine starts with the empty witness prefix, expands the frontier,
prunes with the disjunctive hard reduction, and runs the original verifier on surviving
leaves. The checked loop is polynomial in the original input length under the stated
hypothesis. It does not call the target language's membership oracle.

`CollapseIffSparseHard` converts exact-length sparsity to cumulative sparsity and proves
the converse using reduction to the empty-word singleton. These are exact conditional
results about the pinned classes. The sparse NP-hard target is a hypothesis.

## Measured sparse-frontier machines

`PolynomialImageMembership` searches an encoded frontier for a specified disjunctive
reduction image in polynomial time. `SparsePruningMachine` realizes the sparse pruning
algorithm on explicit word encodings, with the cardinality cap supplied in unary.
`FrontierExpansionMachine` lifts a polynomial-time child-producing function to a
polynomial-time flat map of the encoded frontier. These are reference Turing-machine
results and use the original tagged encoding for calls to the reduction.

## Disjunctive reduction and sparse candidate frontiers

`DisjunctiveHardImage` builds a polynomial-time map on the reference tagged pair
encoding. For an NP language and an NP-hard target, the mapped pair belongs to the target
exactly when at least one component belongs to the source language.

`SparsePruningAlgorithm` defines a finite list algorithm that uses only image comparisons
and a supplied count bound. It preserves the existence of a source-language member and
keeps at most one more candidate than the bound. `SparseHardFrontier` derives a polynomial
count bound when the target is cumulatively sparse and the source words are length-bounded.
The machine result above supplies this list algorithm’s time guarantee on the indicated encodings.

## Witness recovery in the pinned verifier model

`WitnessSearchOfCollapse` constructs a polynomial-time witness-producing machine for any
reference polynomial-time verifier whose accepted witnesses satisfy a fixed polynomial
length bound, assuming the reference inclusion NP ⊆ P. The suffix-extension query language
belongs to NP. A decider for this language makes greedy prefix extension keep an accepted
completion in reach. The original verifier checks the completed prefix before returning it.

`CollapseIffWitnessSearch` proves the reverse implication for this characterization. A
polynomial-time witness producer for every normal-form verifier yields a P decider for every
NP language by testing the output for a success tag. This is an equivalence with P = NP,
and the proof does not establish either side unconditionally.

`PolynomialWitnessRecovery` returns an accepted witness under the polynomial candidate
coverage hypothesis. It freezes the first accepting candidate and tags it on output, with
the empty output reserved for failure. `ShortSeedWitnessSearch` gives a decision procedure
when each yes-input has a short seed whose polynomial-time decoding supplies an accepted
witness. The decoded witness can be longer than the seed.

## Deterministic verifier search with a polynomial candidate budget

`PolynomialWitnessSearch` generalizes the pinned bounded interpreter search to an arbitrary
polynomial-time verifier. The search enumerates a polynomial number of Boolean words, using
a unary clock evaluated on the input length. The proof bounds the growth of every packed
state by five bits per step and uses the reference measured iterator. If every yes-input has
a witness whose length places it within this prefix of the enumeration, the existential
projection belongs to the pinned class P.

`LogWitnessCollapse` shows that this coverage holds when each yes-input has some witness of
length at most `k * log2 (input length + 1)` for a fixed `k`. The verifier may also accept
longer witnesses. The decision machine uses the polynomial `2 * (input length + 1)^k`.
The length hypothesis is essential. No universal certificate-shortening procedure or
general NP inclusion follows from the construction.

`P_subset_NP` exposes the pinned reference inclusion under the challenge's conventional
target name. It uses the existing reference proof that a verifier can ignore its witness.

## Fixed finite candidate variants

The finite candidate theorems use the reference verifier predicate
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

This checks the revision, copies the submitted modules into the pinned
checkout, refuses to overwrite differing files, and invokes the pinned
exact-statement checker with the included statements collected in `statements.json`. The standard
JSON experiment reports when the isolated environment has no prepared
Lean checkout. It independently compares the archived source and statement hashes to the
record of the separate local exact-statement executions in `reference-check.json`.
Those comparisons identify the files that were checked locally.
