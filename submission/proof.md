# Checking a minimum-weight CNF model is in coNP

The objective counts distinct occurring names which the candidate
assignment sets true. It does not count literal occurrences, and
it does not charge names absent from the formula. An exact polynomial
machine first gathers names using the canonical SAT item encoding
and deduplicates them. The second scan tests each name in the
candidate's true-name word and emits one unary marker per positive
membership. The resulting length equals the cardinality of the
semantic Finset of true occurring names.

The comparator runs that counting machine on the proposed model
and on a possible improvement. A pinned polynomial-time length
decider gives strict comparison of their counts. The generic
coNP upper bound supplies a language accepting legal, length-bounded,
satisfying inputs with no feasible improvement. The witness bound
uses the input length. Any semantic satisfying model contributes a
reference witness of that length, and the canonical witness
agrees with the model on all names occurring in the formula.
Thus the optimum measured through the bit-word comparison is the
same as the mathematical minimum over all satisfying assignments.

The exact kernel check is reproducible with the supplied sources,
statement and pinned reference checkout. The compressed archive
preserves the same XZ bits and exact source hashes.
