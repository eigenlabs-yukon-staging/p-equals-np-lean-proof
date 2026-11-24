The new theorem establishes a structural transformation of strict ternary formulas with variable occurrence counts at most four into strict ternary formulas in which every occurring name has count exactly four. Each output clause has exactly three distinct variable names. The transformation preserves satisfiability in both directions. It works directly on typed formulas and states exact list-position counts, including repeated occurrences in distinct clauses and either polarity.

First double the names in the input formula to make every original name even, preserving each signed literal and its evaluation under restriction. Form the last-occurrence deduplication of the flattened source-name list. For each name in that list, count its source occurrences and attach enough copies of the seven-clause degree-fill gadget to reach four. Every occurring source variable already has at least one occurrence. Hence the number of attachments is between zero and three. All copies allocated for a given source name use its doubled name as a terminal. The five internal names in each copy use an odd-indexed block disjoint from the names used for every other copy. The terminal occurs once in each gadget and the five internal variables each occur four times.

The local proof uses templates for zero, one, two, or three gadgets. It computes their permitted local index range and exact multiplicities. One injective embedding maps local zero to the doubled terminal and every nonzero local index to an odd name. It preserves the distinctness of each clause's projected names. The proof checks that a fresh odd name can occur in at most one block by bounding local offsets and comparing the two block indices. Old names have their old count plus the exact deficit filled at their unique position in the deduplicated list. Those counts use the occurrence bound to avoid truncation ambiguity in the natural subtractions. No count property is needed for names absent from the output.

For the forward satisfiability direction, lift a source assignment so even names use their original values and all odd names are true. The added clauses contain positive internal variables, so each gadget accepts no matter what value the corresponding terminal has. The copied clauses are satisfied by the original assignment. For the reverse direction, any output model satisfies the doubled copy of the original formula. Its restriction to even names therefore gives a satisfying assignment for the original formula. The construction does not assert uniqueness of the choices for fresh variables.

The theorem verifies the formula-level specification. A separate exact target measures the canonical word transducer and proves that its output agrees with this construction. This submission reports the structural theorem and inclusion at the stated rung.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
