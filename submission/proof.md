The theorem concerns formulas whose clauses contain exactly three literals on distinct variables and whose total literal-position count for each variable is at most three. It proves that every such formula is satisfiable in the pinned CNF semantics. This provides the companion boundary to the strict ternary occurrence-four completeness result. The degree condition counts all literal positions of both signs. The distinct variables condition is imposed inside each clause, regardless of sign. Clauses themselves remain an ordered list, and identical clauses may occur at different indices.

The proof works with the finite set of variables in a clause at each list index. Distinctness of the three projected names makes this finite set have cardinality three. To control the number of incident clause positions for a given variable, the proof compares the cardinality of a filtered Fin indexed set with the count of that variable in the flattened list of names. This comparison is proved by induction on the formula. Adding one clause increases the incidence count by one precisely if the variable belongs to the clause's projected name set. In that case the projection has at least one occurrence of the name, which follows from the exact List.count positivity lemma. In the absent case the incidence increment is zero. Flatten distributes over clause cons, so the comparison follows from additivity of occurrence count over append. Consequently each variable is incident with at most three positions.

Apply the indexed Hall satisfiability theorem at d equal to three. Its cardinal inequality is based on counting the incidence edges from any selected family of clauses. The lower bound is three times the number of selected clause positions. The upper bound is three times the size of their neighborhood because each variable is adjacent to at most three positions. Finite Hall’s theorem gives a distinct representative variable for every indexed clause. Assign each representative one of its satisfying polarities in its own clause. Distinctness of the representatives makes all these requirements compatible. All other variables may be assigned false. This witnesses truth of the list-based CNF evaluator.

This argument uses distinctness of the names to pass from a length-three clause to a three-element variable neighborhood. It does not infer the same universal satisfiability for width at most three. Short clauses can have smaller neighborhoods and the Hall hypothesis can fail. Nor does the argument apply directly when the occurrence ceiling rises to four. The checked theorem is a structural satisfiability result and allows every Boolean polarity pattern satisfying its stated syntax. The empty formula is included. This submission reports the pure existence theorem and does not claim that its Hall matching proof is a verified polynomial-time algorithm to extract an assignment.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
