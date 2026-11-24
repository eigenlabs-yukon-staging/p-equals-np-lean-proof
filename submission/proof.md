# A polynomial-time modular evaluator for Boolean coefficient words

The exact theorem constructs a deterministic polynomial-time word transducer that handles a unary-length modulus, a unary-length evaluation point, and a Boolean coefficient list in ascending exponent order. It specifies the canonical pairing byte for byte and returns the residue as a word of repeated true bits. The result is the sum of each Boolean coefficient times the corresponding power of the point, taken modulo the length of the modulus word. The correctness statement requires that the modulus word be nonempty. The transducer and its measured polynomial running time cover all raw input words.

The implementation uses a unary remainder machine. It traverses a dividend's length, maintains a counter, and resets at the modulus length. The remainder machine compares normalized unary lengths, so it also accepts length words whose bits are mixed. Its proof starts with zero, relates each counter to the number of processed bits modulo the modulus length, and proves the result after a traversal of the entire dividend. It also respects the natural-number remainder convention for modulus zero. The measured loop consumes one bit of the dividend per round while keeping the state length within a constant additive growth bound per step.

For the evaluator, the state holds the modulus, evaluation point, unprocessed coefficient word, accumulated residue, and current power modulo the modulus. The scan starts with zero residue and one reduced modulo the modulus as its initial power. It adds the current power when a coefficient is true and multiplies the current power by the evaluation point at every step, reducing both using the remainder machine. The stored residue and power are explicitly truncated to the modulus length. In a correct run these truncations leave the reduced values unchanged. Even on a malformed encoded state both fields then satisfy a size bound in terms of the preserved modulus. This gives the pinned measured iteration lemma a nonincreasing state measure and a linear bound on per-step growth. The scan runs once per coefficient bit.

The calculation proof relates the loop state to a recursive natural-number polynomial evaluator. Congruence under modular addition and multiplication justifies replacing accumulated values by residues after every step. A separate induction on the vector length identifies the recursive value of a list built with List.ofFn with the finite power sum in the exact statement. This approach avoids materializing the unreduced powers. The runtime model is polynomial in unary input lengths, which is the intended setting for the polynomially bounded prime and evaluation point from the witness isolation argument.

The theorem supplies a reusable measured component. It does not itself select a prime, enumerate queries, classify a language in P, or resolve the source decision problem. Its use in isolation is to compare an encoded witness polynomial's value with the residue stored in a query.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
