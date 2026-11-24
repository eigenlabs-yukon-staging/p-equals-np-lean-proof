# Isolation by binary Hankel hashing with short seeds

For a nonempty finite set of vectors over the two-element field, the
statement produces a positive output width k at most n+2. It then proves
that at least one eighth of the seed space yields an affine hash whose
zero fibre meets the set in exactly one element. A seed consists of
n+k diagonal bits and k independent affine offsets. In each row i the
matrix entry in column j is the seed bit at i+j. All probabilities are
presented as inequalities between finite cardinalities.

The algebraic proof uses the previously verified surjectivity of the
matrix action on any nonzero difference vector. For a single input
vector x, each choice of diagonal seed gives exactly one offset vector
that hashes x to zero. There are therefore 2^(n+k) seeds hitting x.
For two distinct inputs x and y, the offset must be the same and the
diagonal seed must send x-y to zero. The measured cardinality argument
uses an additive homomorphism from diagonal seeds to output vectors.
Surjectivity gives a set-theoretic section of that homomorphism.
Translation by the section gives an equivalence between its domain
and the product of its kernel with the output space. In particular the
kernel has size 2^n, since multiplying its size by 2^k gives precisely
the number of diagonal seeds. The joint hitting set is equivalent to
that kernel.

The width is selected so that 2^k is at least twice but at most four
times the size of the source set. For any source element, the set of
seeds hitting it and another element is bounded by summing the pairwise
collision counts over the other elements. Each isolating seed is
associated with one source element, so the disjoint union of those
sets gives the total number of isolating seeds. The width inequalities
make the summed collision penalty at most half of the summed marginal
count. The calculation yields the factor eight in the conclusion.
The proof reuses the finite counting inequality and width-selection
lemma from the earlier full-matrix isolation result. Their premises
are proved for the diagonal-shared family in this submission.

The seed bit bound is n+2k, compared with k(n+1) for sampling every
matrix entry independently. The reduction comes from sharing the
bits on anti-diagonals while retaining the exact pairwise hit counts.
The result is a finite isolation theorem useful for short-tape
randomized reductions. It does not implement a measured generator
or apply the theorem to encoded witness queries in this package.
The artifact includes the exact Lean statement, the original checker
evidence, the needed dependencies, and the separately checked
reference P subset NP target.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
