The theorem proves a sufficient criterion for satisfiability of a finite CNF. Index the clauses by their positions in the input list. The neighborhood of a clause position is the finite set of variable names appearing in that clause. Given a positive natural number d, assume each clause has at least d distinct variables and each variable is incident with at most d clause positions. Then the pinned CNF evaluator has a satisfying assignment. Repeated clauses retain separate indices. Repeated literals in one clause contribute only one incidence edge, and the signed occurrence counts can be larger than the incidence counts.

Fix an arbitrary finite set S of clause indices and write U for the union of their neighborhoods. The proof forms the double sum of indicator values over the rectangle S by U. Summing first by clause gives the sum of neighborhood sizes because every neighbor of a clause selected by S belongs to U. This is at least d times the number of selected clauses. Summing first by variable instead counts the number of selected clause positions incident with each variable. A finite-set inclusion bounds each of those terms by the count over all clause indices, which is at most d. The double sum is therefore bounded by d times the size of U. Positivity of d permits cancellation to establish Hall’s inequality for the chosen set S. The argument takes all finite S, including the empty selection.

The proof invokes finite Hall’s marriage theorem from the pinned Mathlib to obtain an injective map from clause positions to variable names. Each image belongs to the neighborhood of that position. For each clause position, membership in its projected name set gives a literal of the matching variable with some Boolean polarity. Choose one such polarity. On matched variables set the assignment to that polarity and set other variables to false. Injectivity is used explicitly to prove that the finite matching gives a well-defined choice for each matched variable. Every indexed clause thus has a literal that evaluates to true, and the conjunction evaluator returns true.

This applies even when different clauses disagree on the desired polarity of a shared variable, since each matched variable is assigned on behalf of only one clause. The positivity condition is essential to the given conclusion: taking d zero would permit a formula containing an empty clause. The formula with no clauses is covered by the proof. In particular, a formula with three distinct variables in every clause and at most three clause positions incident with any variable satisfies the criterion at d equal to three. The proof gives a mathematical existence theorem with independent finite reasoning in the reference formula type. It makes no claim about a measured Lean machine for finding the matching.

The public target uses Fin-indexed clause positions, list projection to variable names and finite-set cardinalities stated directly in the theorem. The supporting declarations isolate the double-counting step and the construction of a satisfying assignment from the matching. The separate reference checker statement can therefore be compared without making its text depend on the helper declarations. This result is submitted as a supporting SAT theorem at the inclusion milestone.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
