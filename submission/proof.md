# Pinned NP verification for a unary witness threshold

`ThresholdWitnessNP.lean` proves an unconditional NP upper bound for the
language asking whether a polynomial-time verifier has a unary number of
distinct accepted witnesses. The certificate is an encoded strictly
increasing list. Each measured step decodes and verifies one record,
checks strict order, and advances. The proof establishes soundness even
for malformed raw certificates and supplies a polynomial certificate
bound measured in the entire tagged query length.

## Conditional deterministic threshold and enumeration

`TruthTableSparseWitnessEnumeration.lean` returns the encoded ordered
prefix of all accepted witnesses, with the requested number specified
by the length of the budget word. The machine iterates the measured
lexicographic successor and appends each witness once. A cap on the
tagged result bounds state growth, and the original verifier relation
gives a finite sorted list describing the exact output.

The replay record includes the exact Lean statements together with their
hashes and the recorded transitive source hashes.

## The measured successor

`TruthTableSparseNextWitness.lean` accepts a verifier input and a cursor.
The empty cursor requests the first witness. A nonempty cursor requests
the least witness strictly after its tail. The result is an unambiguous
true-tagged witness or an empty word if no eligible witness exists.
Repeated use with the previous successful output enumerates successive
witnesses with polynomial delay under the bounded sparse reduction
hypotheses.

## Ordered witness selection

`LexTruthTableSparseWitness.lean` returns the least accepted witness in
ordinary Boolean-word lexicographic order under the bounded sparse
reduction hypotheses. The encoding replaces each witness bit b with the
pair of bits true and b, ends with a false marker, and pads to a fixed
length. Measured scans implement the encoding and decoding. Comparing
two encodings preserves a differing witness bit and orders a proper
prefix before its extensions. A canonical verifier accepts exactly the
padded forms of the original accepted witnesses.

## Shortest witnesses and exact-length search

`ShortlexTruthTableSparseWitness.lean` handles any measured verifier relation
whose accepted witnesses have polynomially bounded lengths. It returns a
shortest accepted witness and breaks length ties lexicographically. The
canonical padding verifier checks a unique fixed-length encoding for each
accepted word. Lexicographic order of those encodings agrees with the
length-first comparison. The earlier exact-length producer selects the
least encoding and a measured projection decodes the underlying witness.
All witness and collapse results use explicit sparse reduction hypotheses.

## Exact-length search and collapse

`VariableTruthTableSparseWitness.lean` constructs a polynomial-time function
that returns the least accepted exact-length witness, tagged with a leading
true bit, or the empty word exactly when the verifier has no witness. The
encoded frontier remains decreasing by witness prefix and keeps the least
valid witness's prefix whenever that witness exists. At full depth, a
measured filter retains exactly the genuine candidates.

`LastEncodedMatch.lean` proves the reference polynomial-time machine
selects the last matching word from a tagged encoded list. The witness
producer uses this operation to recover the least accepted word in the
ordered final frontier. Testing the result for nonemptiness gives the
conditional decision route used by the existing adaptive and nonadaptive
reductions.

## Pruning and conditional collapse

`DirectionalTruthTableTrim.lean` proves that a known false default requires
only the first m records and a known true default requires only the last m+1
records, where m bounds the number of exceptional positions. An exact
boundary remains in the retained segment in each case.

`MeasuredCompressedTruthBoundary.lean` applies this result to the two stable
groups obtained by evaluating the table on the all-false vector. Inside a
query-word fiber, the machine uses both restrictions of the selected
Boolean coordinate. It merges their recursive selections in frontier
order. For every sparse membership assignment making the frontier true
followed by false, the encoded output retains its last true candidate.

## Earlier conditional collapse theorems

`AdaptiveTranscriptSparseCollapse.lean` accepts a constant number of adaptive
queries, a measured query generator on the pair of input and previously observed
bits, and a measured leaf decision on the pair of input and full transcript.
The compiler considers the fixed finite family of all possible histories.
Every hypothetical answer vector determines one transcript, so the matching
table entry runs the measured leaf decision with that transcript supplied as
a constant. An induction on the remaining rounds proves correspondence with
actual target membership.

`AdaptiveTranscriptCoSparseCollapse.lean` gives the coNP-hard version using
the complement of the source language and a measured negation of the leaf
decision. Both adaptive theorems have explicit hardness, reduction
correctness, and sparsity hypotheses.

`EncodedTruthTableSparseCollapse.lean` proves a conditional route to
`PEqualNP.Library.P = PEqualNP.Library.NP`. Its hypotheses are an NP-hard source,
a cumulatively polynomially sparse target, a constant number of nonadaptive
queries, a polynomial-time generator of an encoded query vector and Boolean
table, and the exact language equivalence when that table is evaluated on the
target membership bits. The theorem supplies neither an NP-hard source's
reduction to a sparse set nor an unconditional NP decision algorithm.

`VariableTruthTableSparseCollapse.lean` accepts the queries and table bits as
separately measured functions. It derives the collapse through a frontier over
equal-length witness prefixes, ordered so the last true prefix query is the
prefix of the lexicographically least valid witness. The query width derives
from the machine output length theorem, and the sparse count bounds the
finitely many accepted words at that width. The proof never computes the
accepted-word set. It quantifies over that set when proving correctness for
pruners that only inspect the generated words and table bits.

`BoundedTruthTableBoundary.lean` proves the finite fixed-table bound.
The measured compiler in `MeasuredBoundedTruthTableBoundary.lean` realizes
the passes over encoded lists, with `FiberCompressionPass.lean` implementing
one coordinate-value pass. The cap on a fiber at each stage comes from
sparsity and the suffix retained as a certificate for every possible last
true candidate. `OrderedSparseFrontierSolver.lean` lifts these pruning
guarantees into a decision machine, using a size-capped loop and a terminal
verifier check. `P_subset_NP.lean` separately checks the pinned reference's
unconditional reverse inclusion.

The supplied `check.py --reference /path/to/pinned/checkout` copies the source
overlays to the specified checkout and runs the reference checker on the
public statements against the pinned definitions. The hosted Python
experiment hashes the source and exact statements against the recorded
local checks when the reference checkout is absent. It reports zero kernel
checks for that mode.
