The new theorem constructs a single deterministic polynomial-time function on the pinned CNF word encoding. On formulas with clauses of width at most three and occurrence cap five, it returns exactly the encoded formula with three distinct names in every clause and occurrence cap five. The theorem also proves equivalence of model types on the actual finite name sets. Unsatisfiable, unique, and multiple-model cases are all preserved.

The formula specification keeps every original variable, even in a tautological clause. The machine reads up to three literal tokens, and tests whether any pair has equal variable-code tails and different full words. That is exactly the opposite-polarity condition. In the non-tautological case, measured pairwise keep operations remove all but the last occurrence of an identical literal word. In the tautological case, each present word is first made positive, so those same comparisons deduplicate by variable rather than by signed literal. The typed proof compares the three optional raw word slots with the encoded literal list, and derives the exact last-occurrence deduplication. Distinct old names are doubled. The number of missing slots determines one of four fixed local output templates, and the taut flag determines the polarity of the first padding literal. A tautological input of width at most three necessarily has fewer than three distinct names and thus has space for the guaranteed true negative terminal. No literal is available from the empty token value.

Each missing slot receives a fresh odd terminal and an eleven-clause, seven-variable gadget. The gadget has only the all-false model, and its terminal occurs four times internally and once in the containing padded clause. The three possible local offsets use at most twenty-one odd positions. The binary base advances by twenty-one after each source clause. On arbitrary words the scanner consumes at least one bit whenever its remaining input is nonempty. Its base grows by at most twenty-one bits per step, and the maximum number of possible template occurrences per scanned clause is constant. A nonincreasing measure combines twenty-one times the remaining length and the current base length. The output extension is bounded by a fixed multiple of that measure plus a constant. The pinned measured iteration theorem gives polynomial time for iteration up to the original input length.

For a canonical encoded formula the proof inducts on the source clauses and shows the exact consumed delimiter, exact block bytes, and binary base update for each step. The mathematical maps between source and target models lift original values to the even names, fill each odd used name with false, and restrict back to the even names. The support and zero-value theorems show they are inverse on the finite domains. The polynomial-time claim uses the measured encoded computation, while the bijection concerns the reference model evaluator on the particular returned formula. No deterministic decision procedure for unrestricted SAT is asserted.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
