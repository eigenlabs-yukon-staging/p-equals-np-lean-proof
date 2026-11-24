# Constant-round adaptive reductions to sparse targets

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

`VariableTruthTableBoundary.lean` uses finite enumeration of functions
`(Fin k → Bool) → Bool`. Each table determines a stable subsequence of candidates.
For the group containing the global last true candidate, that candidate is
also the last true one in its group. A fixed-table pruning pass retains it.
The machine filters the original frontier against the selected groups so
the remaining candidates retain their original order.

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
