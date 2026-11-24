The theorem proves a lower bound for a strict ternary CNF that has exactly one model on a specified finite set of variable indices. Every clause has three distinct names, all indices lie below n, every variable occurs at most four times, and one chosen terminal is permitted at most three occurrences. The bound is n at least ten. The theorem permits variable indices that are unused, but uniqueness itself is interpreted over the entire indicated Fin n function space. No SAT solver conclusion enters its proof.

First normalize the unique model to the all-false assignment. For each old variable that the unique model sets true, flip the sign of every occurrence of that variable. The evaluator under an assignment to the flipped formula agrees with the original evaluator under pointwise sign transport on assignments. The proof checks that clause lengths, projected variable-name lists, and total occurrence counts do not change. It also proves that the ambient domain must have at least three names under the premises. A nonempty strict ternary formula already contains a three-element variable set. An empty formula with a terminal in the domain has at least two assignments.

In the normalized formula, every assignment with just one true name is rejected. Since the all-false assignment satisfies, a clause rejecting that singleton must have exactly one negative literal, on the singleton name. Conversely, rejecting the all-true assignment requires an all-negative clause. Pick one singleton blocker per variable. They are distinct because their sole negative names differ, and the all-negative clause is distinct because it has three different negative names. If the formula had at most n plus two clauses, at most one distinct additional clause would remain.

The proof constructs another model from an assignment with at most two variables set false and all others true. When there is no extra clause, choose one negative name from the all-negative clause. The two positive names in each singleton blocker are distinct, so deleting one name cannot falsify the blocker. When an extra clause exists, select any negative name v in it. If the all-negative clause also contains v, deleting v alone satisfies both exceptional clauses. Otherwise select a name e from the three names in the all-negative clause that never occurs together with v as the two positive literals in a chosen blocker. Such an e exists because v already appears negatively in its own blocker and in the extra clause. There are at most two remaining positive positions for v, each able to block at most one choice of e. Deleting v and e therefore satisfies both exceptional clauses and leaves a true positive literal in each blocker. At least one variable remains true. This contradicts uniqueness, so there must be at least n plus three clauses.

Counting all literal positions now gives three times the clause count. The degree cap gives a strict upper bound of four times n because the terminal loses one position. Combining the two inequalities yields the claimed lower bound. The result does not assert existence at ten or an optimal upper bound. It supplies an exact structural constraint for attempts to improve the submitted parsimonious padding gadget.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
