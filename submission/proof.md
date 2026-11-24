# Minimum-weight CNF model recognition is coNP-complete

Starting with arbitrary source CNF, reserve selector zero and
rename source variable i to 2i+1. Insert a selector tautology and
add the positive selector to each renamed clause. For every
occurring original name i, append a clause requiring a penalty name
4i+2 to be true when the selector is true. It is safe to emit this
clause repeatedly for repeated original occurrences. The objective
charges distinct names, so repeats add no weight.

The fallback sets only the selector and the penalty names true.
Its weight is one plus the number of distinct original names.
This is proved by exact cardinalities and odd/even separation.
Every satisfying assignment with the selector true must also set
every penalty name true, so it cannot be lighter. If the source
formula is satisfiable, lift a source assignment using the odd
names, leaving the selector and all penalty names false. It has
weight at most the number of original names and is strictly
lighter. If the source is unsatisfiable, every satisfying target
assignment has the selector true, so the fallback is minimum.

A polynomial raw-word reduction computes the renamed gated CNF
and the penalty suffix from the actual bit encoding. The companion
witness scan emits the selector and penalty names and its length is
bounded by the encoded target formula. The compiler proof covers
an arbitrary raw input and maps malformed words to the image of
an unsatisfiable single-empty-clause formula. The coNP upper bound
and the pinned SAT completeness theorem complete the classification.

Exact theorem statement and complete proof source are supplied.
The reproduction harness and mixed archive preserve source bytes
and distinguish actual verifier execution from hash comparison.
