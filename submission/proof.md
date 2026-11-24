# A formula-level reduction to a positive binary CNF weight bound

The checked theorem constructs a monotone CNF with at most two
literals per clause and a cardinality budget. It proves that an
arbitrary source CNF is satisfiable exactly when the constructed
formula has a satisfying assignment whose number of distinct true
occurring variables is within the budget. This is the semantic
component of a reduction. The statement does not yet establish a
polynomial-time implementation of the map on the reference
encoding.

There is one vertex for every literal occurrence, kept distinct
even when a literal repeats. Two distinct vertices conflict when
they belong to the same clause or give opposite values to the same
original variable. An independent set of size at least the number
of original clauses has exactly one selected occurrence per clause
and induces a consistent assignment satisfying the source. A
satisfying source assignment yields such an independent set by
choosing one true occurrence in each clause.

The target formula makes each conflicting pair a positive binary
clause. Target variables set false are the selected independent
vertices. A global anchor and one marker per original clause are
forced true. The global anchor also ensures each vertex is present
in the target name set, even if it has no incident conflict. If
there are T occurrences and M clauses, the count of true names
plus selected vertices is T + M + 1. Setting the budget to T + 1
therefore forces at least M selected vertices. Empty clauses,
empty formulas and repeated literal occurrences are covered.

The exact source and statement hashes are supplied with the pinned
checker record. The actual kernel check is reproducible from the
submitted source and prepared reference checkout.
