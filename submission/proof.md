The new finite theorem supplies a seven-clause gadget whose clauses each consist of exactly three distinct variable names. The gadget uses variable names zero through five. Its terminal, name zero, occurs in a single literal position, and each of the five internal names occurs in exactly four literal positions. Assigning all internal variables true satisfies the whole gadget under either value of the terminal. This allows a formula transformation to add one occurrence to an existing variable by using name zero for that variable and mapping the internal names to fresh variables.

The construction starts with the clause on zero, one, and two. For the other six clauses, take complements of six pairs within the set consisting of one through five. Those pairs are (one, two), (one, three), (one, four), (two, five), (two, three), and (four, five). Their multiplicities are three for one and two, and two for each other name. Complementing each pair gives a triple, so each of one and two occurs three times among the six triples and the other three names occur four times. The first clause adds one more occurrence for one and two. Every literal in the gadget is positive. This explains why the five all-true internal values suffice even if the terminal value is false.

The Lean declaration displays all seven clauses explicitly in the pinned CNF type. It checks exact widths, projected-name distinctness, and that every used name is less than six using the kernel's decidable proof path. For the degree identity it splits the bounded variable index into the six natural-number cases and computes the flattened-list count. This ensures that the result counts literal occurrences with multiplicity, including positions in separate clauses. No enumerable domain for arbitrary assignments is assumed in the semantic result. The proof takes any total Boolean assignment, instantiates its hypothesis for each of the five internal names, and unfolds the pinned literal, clause and formula evaluators under both cases for the terminal. The resulting Boolean computations give the required evaluator equality.

To reuse the gadget for degree completion, distinct fresh groups are needed for separate attachments so that all new names keep degree four. Each application raises the count of its existing terminal by exactly one. A variable already of degree four requires no attachments. The gadget proof alone does not build a global regularization function, bound its runtime, or establish a complexity-class conclusion. It supplies the checked local formula and semantics for those later steps. The all-true extension is chosen as a convenient witness and no uniqueness claim is made. This is submitted at the inclusion rung together with its exact reference-checked supporting theorem.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
