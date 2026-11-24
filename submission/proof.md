# Prime-field hashing in a measured bounded-witness verifier

The theorem starts with a relation R that is decidable by a measured machine on the pinned encoding of word pairs, and a natural-coefficient witness cap p. For each source word x it defines the finite set W(x) of words accepted by R whose length is at most p evaluated on the length of x. It supplies a measured Boolean query verifier D, proves that the existential query language belongs to the pinned NP class, and proves that every accepted witness for a query carrying x belongs to W(x). The result then bounds the parameters of a query that isolates any selected member of W(x).

First the verifier checks the bound at the source word and tests the original relation. The same witness is encoded into a fixed-length Boolean word with an injective length-and-content representation on bounded words. The query also carries three unary records. The machine extracts their modulus, point, and target residue, invokes the measured modular evaluator on the fixed-length coefficient word, and compares the resulting unary word with the target. The encoded-pair parser and the composed polynomial-time witnesses are included in the checked development. The witness guard applies even to noncanonical hash parameters so arbitrary parameter words cannot generate false positives for a source instance with no witnesses.

When the witness count is at most m, the finite separation theorem gives a prime q no larger than 2 times (m squared times the coefficient width, plus one). The coefficient width is 2p(|x|)+1. The proof obtains an evaluation point whose field value distinguishes every bounded witness in W(x), via the injective embedding into fixed-length bit vectors. The point and target residue use their natural representatives strictly below q. The formal calculation transports the machine's natural-number modular result to the prime field, identifies its finite power sum, and uses injectivity to show that any accepted witness equals the selected one. This is a uniqueness statement over all raw witness words, because feasibility was already checked separately.

The NP membership proof uses the original witness word as the certificate to the query. The source word occupies a bounded portion of the raw query, so the witness guard at the source implies the ambient polynomial bound at the query. A measured verifier for the exact relation and the resulting witness equivalence therefore give the pinned NP introduction judgment directly.

This isolates the transition from the finite field counting argument to executable witness verification. A polynomial upper bound on m makes the displayed unary parameters polynomial in source length. The theorem gives the explicit local existence of an isolating tuple under any numerical witness bound and makes no universal multiplicity assumption. A deterministic query generator still needs a supplied polynomial bound on m, and a deterministic source decision statement needs the specified query oracle. This submission concerns the query verifier, its correctness, and NP membership.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
