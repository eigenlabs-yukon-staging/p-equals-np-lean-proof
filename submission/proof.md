# The exactly-one-witness predicate as a difference of NP languages

Fix a word-pair relation R with a decider in the pinned polynomial-time representation, and a natural-coefficient polynomial p. A feasible witness for a word x is a Boolean word w satisfying R at (x,w) and the length bound p evaluated at the length of x. The first exact theorem constructs a language in the pinned NP class containing precisely the words that have two distinct feasible witnesses. The second theorem expresses the predicate of having exactly one feasible witness as A minus B, with both A and B in pinned NP. The two statements use the same verifier and the same witness bound on each component.

The existential certificate for the first theorem encodes the two words using the reference's Boolean pairing. The polynomial-time witness verifier parses the certificate, checks each component against the original relation and the original length bound, and compares the components for inequality. These checks use the pinned transducer calculus. In particular, the comparison uses the Boolean word contents, so two different words of the same length can form a valid pair and repetition of the same valid word cannot. The certificate size bound is three times p evaluated on the source length plus one. This bound accounts for the asymmetric cost of the reference pair encoding, where the first word contributes twice its length and the second word once.

Soundness starts from a certificate accepted by the explicit machine. Its decoded words satisfy the two guards and are unequal. This argument works regardless of which raw certificate words are valid canonical encodings. Completeness starts with two distinct bounded witnesses, encodes them, and uses the exact pair round trip and length formula to show that the resulting certificate is accepted and fits within the polynomial bound. These directions establish the language equality required by the pinned NP definition rather than relying on a complexity claim about an unimplemented Lean function.

For the difference theorem, A uses R and p directly as an NP verifier. B is the language from the first theorem. A word in A has some feasible witness, and membership outside B says there cannot be two distinct witnesses. Conversely, existence of a unique witness gives membership in A, and any two components claimed to witness membership in B must be equal by uniqueness. This places the exact-one predicate in the usual difference form associated with DP, using the challenge's own language and NP encodings. The theorem makes no DP-hardness or completeness claim.

The result isolates an important distinction for promise arguments. A decision procedure for zero versus exactly one witness can behave arbitrarily on inputs with two or more witnesses, whereas the exact-one language gives a specified negative answer there. The difference characterization is about the latter total language. It does not provide either decider in deterministic polynomial time. Its value for the isolation development is to characterize what a hypothetical exact-one oracle would decide and to give the stronger counting guard a concrete certificate implementation.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
