# Variable-width conjunctive reductions from NP-hard languages

`ConjunctiveSparseCollapse` constructs a deterministic polynomial-time reference
machine from a polynomial-time conjunctive reduction of a pinned NP-hard language
to a cumulatively sparse target. It normalizes witnesses to a fixed length, computes
lexicographic prefix-boundary queries and preserves the least accepting witness by a
measured ordered pruning procedure. The precise reduction and sparsity hypotheses
remain explicit premises.

`ExactWitnessPadding`, `LexicographicWordCompare`, `LexPrefixQueryNP`,
`SparseConjunctiveBoundary` and `MeasuredSparseConjunctiveBoundary` are also checked
as separate targets.

## Variable-width conjunctive reductions to sparse targets

`ConjunctiveCoSparseCollapse` proves the pinned equality P = NP when a coNP-hard
language has a polynomial-time conjunctive reduction to a cumulatively sparse
target. The query generator can emit any encoded list its polynomial-time
machine can produce. `CoSparseQueryFrontier` supplies the measured pruning step.
A candidate remains only if it introduces a new query. The union of queries
is preserved, and too many retained candidates certify that some query lies
outside the sparse set. The collapse is conditional on the stated reduction.

## Bounded conjunctive reductions to sparse targets

`BoundedConjunctiveSparseCollapse` packs the fixed-width query list of a conjunctive
reduction into one word. Its sparse tuple language has counting polynomial
`(q + 1)^k`, where `q` bounds cumulative target density and `k` bounds the number
of queries. If the source is NP-hard or coNP-hard, the exact pinned many-one
collapse implication applies to this new sparse target.

## Structure of hard languages and the pinned equality

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
