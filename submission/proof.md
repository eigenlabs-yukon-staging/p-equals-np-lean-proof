# Isolated NP query batches from a fixed uniform coin tape

For each pinned NP language the theorem builds a polynomial-time
query generator and a polynomial-time query verifier. The
generator receives the input and an explicit tape of
(2b + 3)(2b + 2) Boolean variables, with b the reference
polynomial bound on source witness length. It outputs the
encoded list of prefix queries. The existentially described
query list is the exact output of the real measured word machine.

The affine matrix encoding is a bijection onto all tapes of that
length. An exact finite-cardinality transfer therefore moves the
successful event from full affine matrices to the entire Boolean
tape space, with no missing or duplicated tapes. For every yes
input, at least an eighth of the tapes generate a query with one
accepted witness. Every accepted witness of a generated query
is also a bounded original witness, which proves the same
uniqueness over all raw witness words. All queries on a source
no-input reject every potential witness.

This is a finite formulation of a randomized reduction to
isolated witness queries. The two functions are ordinary
reference polynomial-time deterministic machines taking the
random tape as data. The result does not assume a solver for
the isolated-witness promise, claim that the full query language
has unique witnesses, or assert a deterministic P = NP result.
