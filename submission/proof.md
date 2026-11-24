The theorem proves an equisatisfiable construction from width-at-most-three CNF of occurrence degree at most three to exact-width-three CNF of occurrence degree at most four. Each output clause contains three distinct variable names. The width and degree premises concern literal positions in the input formula. The output degree also uses flattened literal positions so the statement tracks signs separately during projection and counts every occurrence of a variable name.

The proof first normalizes the formula. It recognizes clauses that contain both signs of a single variable and drops them because they are true under every assignment. In each remaining clause it removes repeated signed literals. This preserves the clause evaluator and cannot increase any variable's occurrence count, since the flattened normalized literal list is a sublist of the original. After removing duplicates in a non-tautological clause, two distinct remaining literals cannot project to the same variable name. If they did, their polarities would differ and the clause would have been removed.

For every retained clause, its original variable indices become even names. For each of its zero through three missing slots, the construction adds a positive literal on an odd fresh name and attaches a translated copy of the four-variable terminal gadget. Its local terminal is forced false in any satisfying assignment. The gadget itself has exact width three and distinct variables within each clause. Its terminal has three occurrences inside the gadget and one in the padded clause, and every other local variable has four occurrences. The affine fresh-name layout allocates twelve odd positions per retained clause. The proof checks the local ceiling for all three possible gadget copies, proves the offsets cannot collide across different clause positions, and separately uses the injective doubling map to count all original even names.

To prove satisfiability forward, extend a source assignment along the even-name map and give all odd names value false. Every gadget accepts the all-false local assignment, and a source literal satisfying an original retained clause also satisfies the padded clause. Conversely, any satisfying output assignment satisfies every gadget and so gives all of the added positive literals value false. The assignment restricted to even variables then satisfies every normalized clause. The earlier normalization theorem recovers a satisfying assignment of the original formula. Formulas with no clauses or with an empty clause are included by the same construction. An empty source clause receives three forced-false literals and remains unsatisfiable.

This target verifies the structural and semantic proof. The measured transducer that computes this transformation on canonical words requires separate evidence from a later result. The number of satisfying assignments need not be preserved since a gadget admits several models. The new theorem therefore concerns existence of models and is submitted as a checked supporting result at the inclusion rung.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
