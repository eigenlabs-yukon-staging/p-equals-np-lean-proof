# Isolated queries from one fixed-size affine seed

The theorem strengthens the good-width guarantee for seeded NP
witness verification. A good width exists for each input in the
original NP language, but its identity can depend on the number
of witnesses. Instead of requiring the width up front, take one
affine seed with the maximum permitted number of rows and
consider every nonempty prefix. For at least one eighth of the
full seeds, some prefix yields a query with one accepting
bounded witness.

For an arbitrary shorter width, there is an explicit equivalence
between a full row function and its prefix and suffix. The prefix
consists of the first indexed rows, and the inverse appends the
suffix by subtracting the prefix width from each later index.
Finite product cardinalities show that every prefix has the
same number of extensions. Therefore a one-eighth success
fraction at any width lifts to at least the same fraction over
full seeds. A full seed is successful when any one of its
prefixes is successful, so the property only grows.

The pinned polynomial-time verifier and its NP query language
come from the measured affine row checker. The theorem keeps
the original no-input guarantee for all possible raw seed words.
It also gives the equivalence between query-language membership
and existence of an accepting verifier witness. No assumption
about finding a good width or counting the source witnesses is
needed. This is the finite cardinality property for the
fixed-size family. The theorem does not implement the batch
serialization of every prefix query or a random number generator.
