# One-sided simulation under an isolated-query promise oracle

For every pinned NP language the theorem constructs a seeded
query verifier, its query language in NP, and a polynomial
number of explicit Boolean coin bits. It then quantifies over
a hypothetical polynomial-time oracle that answers false on
queries with no accepted witness and true on queries with
exactly one accepted witness. The oracle can answer either way
on a query with multiple witnesses.

Under those assumptions, a polynomial-time paired-input
machine constructs the affine prefix query batch, evaluates
the assumed oracle on each query, and returns their Boolean
disjunction. The list scan uses the canonical raw pairing
encoding and a measured loop. A polynomial unary clock
computes and checks the required tape length. On any source
no-input the simulated result is false, including at malformed
tape lengths. For every source yes-input at least one eighth
of the exact-length tapes yield a true result.

The yes proof uses the checked finite isolation property.
An isolated batch query has one accepted witness in the
finite source witness set. All accepted query witnesses lie
in that set, so the promise is satisfied over all raw witness
words. The proof assumes the oracle and does not claim that
such an oracle has been constructed or that arbitrary NP
languages are deterministically decidable in polynomial time.
