# Exact finite bijection between affine matrices and bit tapes

The checked map takes a matrix of m affine rows over the
two-element field, each of dimension 2b + 1, to the
concatenation of its row encodings. A row begins with its
offset bit and continues with its coefficient bits in index
order. The resulting length is exactly m times (2b + 2).

Injectivity is proved through the actual row organization.
Splitting the word into fixed-size blocks recovers the
canonical encoded record list. One-to-one decoding of the
unary-prefixed pairing recovers the individual rows. Equality
of the bit representation forces equality of every field
coordinate, because Boolean serialization and field coercion
are inverse on the two-element field.

The finite type of tapes of a specified length is equivalent
to a finite-indexed Boolean function. Its cardinal equals the
power of two for that length. The same product calculation
gives the number of affine matrices. An injection between the
two finite sets of equal size is surjective, so every exact
length Boolean tape is the encoding of one and only one matrix,
including the zero-row case. This permits transporting uniform
counts between the mathematical seed matrices and raw tapes
used by the batch-query machine.
