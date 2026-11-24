# Deterministic coordinate isolation for small finite families

Any finite set of Boolean vectors admits a separating set
of at most one fewer coordinates than its cardinality.
Insert vectors one at a time. The previously chosen
coordinates leave at most one old vector indistinguishable
from the new vector. If that old vector exists, choose a
coordinate where it differs from the new vector and add it.
Old vectors remain separated, and the new coordinate
separates the only unresolved pair. The empty and singleton
cases both need zero coordinates.

For a set of cardinality at most c + 1, a pattern with c
optional coordinate tests can isolate each member. Copy its
values on the selected separating coordinates and leave the
remaining slots blank. There are exactly (1 + 2n)^c such
patterns on n Boolean coordinates. With c fixed, this is a
polynomial-size family, giving a finite combinatorial
ingredient for deterministic isolation of bounded
multiplicity witness sets.

The statement verifies the separating coordinates, singleton
test property, and family cardinality. It does not yet
implement the uniform machine that enumerates or checks the
patterns on words, or assert that arbitrary NP verifier
witness sets have bounded multiplicity.
