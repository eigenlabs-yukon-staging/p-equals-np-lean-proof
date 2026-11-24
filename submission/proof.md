# Affine seed queries with a polynomial-time witness verifier

For each pinned NP language the theorem constructs an NP query
language and an actual polynomial-time verifier. The input to
the query is an encoded pair of the original word and a seed
word. The verifier checks the original relation, the original
polynomial witness size cap and the affine zero-bucket condition
under the supplied seed. For a canonical seed encoding, its
acceptance relation exactly agrees with the finite bounded
witness set and the affine equations.

The witness encoder uses a unary length header and the payload,
padded to their fixed dimensions. Its raw-word transducer computes
the padding with a finite-state fill and a measured drop. An item
scanner computes XOR dot products by stepping through coefficient
and witness bits together. A second bounded scan visits the paired
rows and rejects if a bias-adjusted dot product is nonzero. The
semantic proof connects Boolean parity to addition and multiplication
in the two-element field. The reference polynomial clock supplies
the dimension from the length of the original source input.

For every source yes-input there is an output width at most the
encoded witness dimension plus two with at least a one eighth
fraction of seeds accepting exactly one bounded witness. A source
no-input has no accepting witness for any raw seed word, including
malformed seed words. The original witness test is retained in
every branch. The theorem supplies the seeded verifier and its
finite success guarantee, without assuming an algorithm for the
original NP language or implementing a random seed sampler.
