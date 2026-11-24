# Minimum-weight Horn model extraction

A verified polynomial-time function returns the true-name word of
the least model of any given satisfiable Horn CNF. The formal
statement gives its exact witness representation, full formula
satisfaction, and the fact every true variable in the returned
model must be true in every satisfying assignment. Consequently
the result minimizes the number of distinct true names appearing
in the original formula.

The machine reuses the saturating positive-unit propagation
state from the earlier Horn decision development. Each propagation
step sets a fresh forced name, and the number of distinct occurring
names is at most the input word length. The final iteration count
therefore reaches a fixed state. The semantic proof maintains
that every name collected by propagation is true in any satisfying
assignment. At the fixed state, every retained clause still has
at most one positive literal. A retained empty clause conflicts with
the satisfiability hypothesis. A retained all-positive nonempty
clause would thus be a positive unit and contradict saturation.
Every remaining clause contains a negative literal, so taking all
unassigned names to be false satisfies the residual CNF. Combine
that assignment with the propagated names to satisfy the input.

The resulting finite set of true occurring names is a subset of
that of any feasible model, which proves the weight inequality.
There is no cap on the number of variables or clauses beyond the
pinned polynomial runtime measured against their actual encoding.
The exact statement concerns the satisfiable Horn domain.
