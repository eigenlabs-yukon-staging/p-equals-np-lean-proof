# Prime-field polynomial evaluation for finite Boolean witness sets

A finite set of Boolean vectors admits a single polynomial evaluation that distinguishes every member, over a prime field whose order is at most twice the number of ordered pairs times the dimension, plus two. The exact Lean theorem quantifies over the dimension and every finite set of vectors of that dimension. Its lower bound on the prime, its upper bound on the prime, and the evaluation's injectivity on the supplied set all appear in the intended statement. The theorem also covers empty and singleton sets and vectors of dimension zero.

A vector represents a polynomial with one coefficient per coordinate, with Boolean false interpreted as zero and true as one. Distinct vectors yield distinct polynomials because equality of their coefficients recovers every bit. The difference for a distinct pair has degree at most the dimension. The corresponding finite field root set bounds the number of evaluation points that make the pair collide. Define the collision contribution for an equal pair to be empty. That convention lets the proof take the union over the whole Cartesian square without conflating the root bound for a nonzero polynomial with the zero polynomial case.

For the set S, the union of collision sets has size at most |S|² times the dimension. The field cardinality exceeds that bound, so the union cannot contain the entire field. Select an evaluation point outside the union and use the root characterization on the difference to prove injectivity. Bertrand's postulate supplies a prime q larger than |S|² times the dimension plus one and no larger than twice that quantity. Mathlib supplies the existence theorem and the facts about roots and the cardinality of ZMod q. The submission instantiates those results and verifies the finite collision argument rather than relying on a new primality algorithm.

For polynomially bounded witness multiplicity and polynomial witness bit length, the theorem bounds q polynomially in the original input length. Consequently the prime, the evaluation point, and the evaluation residue of a chosen witness can each fit in a polynomially bounded unary word. An isolation family can consider every such triple. For the particular prime and point given by this theorem, each existing witness has a residue shared by no other witness. That is the intended connection to witness isolation for NP verifiers.

This submission covers the finite mathematical step. A future machine proof must construct the query enumerator, implement modular evaluation on the word representation, and show that these operations compose with the original problem's verifier in the pinned polynomial-time model. An application to a deterministic solver would also need an appropriate promise oracle. The theorem itself requires no oracle and has no assumption that the original NP verifier's witnesses are polynomially bounded. Polynomial multiplicity is the condition under which its explicit bound gives a polynomial-sized search over the three parameters.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
