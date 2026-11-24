# Finite affine witness isolation

For a nonempty finite set of vectors over the two-element field,
some affine output width between one and the input dimension
plus two has at least one eighth of its seeds mapping exactly
one set element to the zero vector. The target counts an entire
finite family uniformly. A seed consists of finitely many
independent rows, each with coefficients and an offset bit.

For one fixed vector, every choice of coefficients determines
exactly one offset producing zero. For two distinct vectors,
some coordinate of their difference is one. The simultaneous
zero condition on one row is equivalent to a homogeneous
constraint on the coefficients followed by the determined
offset. A verified equivalence splits every coefficient vector
into a member of that hyperplane and one independent field
coordinate. Thus each row has exact single-hit and two-hit
cardinalities, and coordinatewise product gives their powers
for multiple rows.

The isolation inequality subtracts collision counts per point
using a finite union bound. The sets of seeds isolating
different individual points are disjoint, so their
cardinalities add. A dyadic output width with its bucket count
between twice and four times the input set size gives the
one-eighth bound. An explicit word encoding carries it to
finite sets of Boolean words with a prescribed length cap.
The encoding uses a unary length header and a zero-padded
payload. The header and payload make the encoding injective
on all words under the cap, including the empty word.

The exact theorems are finite counts. They supply a component
for a witness-isolation reduction. They do not assert
a polynomial-time sampling procedure, a randomized solver
for SAT, or a deterministic class collapse.
