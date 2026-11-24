# Deterministic promise-oracle simulation for polynomial witness multiplicity

The exact theorem starts with a language L, a polynomial-time verifier relation R, a witness length bound p, and a possibly different polynomial r bounding the cardinality of the finite feasible witness set at each input length. It constructs a polynomial-time Boolean query verifier D and an NP language K given by existence of a D witness. It then proves L is in the pinned deterministic P class assuming a measured Boolean function that returns false on every query with no D witness and true on every query with exactly one D witness. Its answer may be either Boolean value on a query with several witnesses.

For a source word x, the sample space for hash parameters is a list of ordered triples of unary records of lengths up to the value of the polynomial 2(r²(2p+1)+1) at the source length. Since this is a natural-coefficient polynomial, the pinned clock theorem yields its unary value in deterministic polynomial time. The list generator uses the tagged coordinate alphabet and three fixed product steps, followed by measured attachment of the original source word to each tuple. The inclusion proof shows that every canonical tuple whose three unary lengths fit the bound occurs in that list. The generator can emit extra parameters. Its semantics ensure that every output has the correct attached source.

The hash verifier rechecks original feasibility, converts the witness into a length-preserving padded bit representation for the stated bound, evaluates its Boolean coefficient polynomial modulo the encoded modulus, and tests equality with the residue in the query. The finite separation theorem gives a prime that fits the clock and a field evaluation separating every witness of a YES input. The representative of the evaluation point and the residue of a chosen witness are both less than the prime. Thus at least one generated query has exactly one D witness. On a NO input, no output of the generator has any D witness, since the guard still tests the original relation and its witness cap for that source. This reasoning does not use any oracle behavior on multiple-witness queries.

To build the final deterministic machine the proof composes the measured generator with an encoded-list scan that computes the disjunction of the assumed oracle's answers. The scan can stop at the first true answer. Each well-formed generated list has the exact membership interpretation used in the proof. On a YES input the isolating query forces a true answer. On a NO input every answer forced by the assumption is false. The theorem then packages that actual polynomial-time machine and the input-language equivalence in the pinned P constructor.

The growth from constant witness multiplicity to a polynomial bound comes from using a constant three parameters, each with a polynomially bounded unary range. The exponent of the tuple product is independent of the number of witnesses. The proof does not supply the assumed decider, a deterministic routine for arbitrary NP without a witness multiplicity bound, or an inclusion NP in P. It is a deterministic reduction with an explicit promise and a fully measured machine construction under that promise.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
