The theorem transforms a typed width-at-most-three formula with occurrence cap five into a strict ternary formula of the same cap. Strict ternary means three literal positions on three distinct variable names in every clause. The result includes an equivalence between satisfying assignments to the sets of actually mentioned names on each side. Both finite models use the pinned convention of setting names outside the formula to false for evaluation. The transformation therefore preserves all accepted assignments, and preserves a zero or singleton model set in particular.

For each clause, collapse duplicate signed literals when the clause is not tautological. Its projected names are now distinct and the evaluator value is unchanged. For a tautological clause, retain one positive literal for each distinct original name. Such a width-at-most-three clause had both signs for some name, so after keeping one name occurrence there is an unused slot. Fill the first such slot with a negative forced-false terminal. The resulting padded clause is true under every gadget-consistent assignment, just like its tautological source. This treatment retains every original variable appearing only in clauses that were already true under all assignments. Simply deleting those clauses would lose model choices. The source-to-target support proof gives an exact equivalence of membership for each doubled original name.

Rename old names to even numbers and place the seven-variable gadget on fresh odd names for every missing literal slot. The gadget has eleven strict ternary clauses with exact degree-table validation. Its terminal occurs four times and occupies one more position in the padded clause. Its full satisfying local model is the all-false assignment, verified by the kernel over the seven Boolean variables. A positive terminal contributes false, as needed for non-tautological or otherwise neutral padding. A negative terminal is used to retain a tautological clause's true value. The roughly twenty-one odd positions allocated to each clause form a disjoint block because gadget offsets are explicitly bounded. The proof counts old-name and fresh-name occurrences separately, and proves no projected name multiplicity increases among cleaned old literals.

The model map reads source values on renamed even names and fills in all fresh names with false. The reverse map reads just the doubled source names from an output model. Semantic proofs for each block show that the source clause holds after that restriction and, conversely, that extending a source model satisfies every output block. Every used odd variable in an output model lies in a gadget or is one of its terminals and therefore has false value. The extension and projection are pointwise inverse on the actual used names, yielding the equivalence in Lean. The theorem is the structural and model-level specification. A companion measured theorem supplies the polynomial word computation. The claim here concerns the checked model-preserving bridge.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
