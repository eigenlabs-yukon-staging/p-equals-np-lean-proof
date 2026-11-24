The checked theorem maps a width-at-most-three CNF to a width-at-most-three CNF with at most three literal occurrences per variable. It gives an equivalence of their satisfying assignment types on the variables that actually occur. Both domains interpret variables outside their finite support as false. The equivalence therefore preserves every bit of a canonical model and implies satisfiability equivalence and preservation of the number of canonical models.

For each literal occurrence the construction allocates its own index. The original clauses retain their order, polarity, and width when names are replaced by these occurrence indices. For each original name, collect the indices at which it occurs. Two or more indices are arranged in a directed cycle and a binary implication is emitted for each directed edge. The empty and singleton cases emit no implications. The cycle constraints force all indices for the same original name to have the same truth value. Each occurrence index appears in its original clause and at most once in each direction in the cycle, yielding the total occurrence cap of three. The added clauses have two positions, so they fit the old width bound without relying on duplicate literals.

The forward map takes an assignment on old names and duplicates each value at all its occurrence indices. Every copied source clause keeps its evaluation, and the copy values satisfy every implication cycle. The reverse map picks the first index in the nonempty group for each used old name. A satisfying transformed assignment agrees with this selected value at every index in the group by the cycle argument. Since each new name belongs to some group and each used old name has a nonempty group, the two maps are inverse on exactly the finite support types appearing in the target. This also handles repeated literals, repeated clauses, and clauses containing both polarities of the same original variable. The empty CNF has no occurrence indices and needs no link clauses.

The proof separates literal indexing, group construction, implication cycles, and model transport into four source modules. It reuses the existing finite support representation from the parsimonious tableau development. It does not rely on a decision procedure for finding a model. The theorem exposes the exact support equivalence independently of any word-level serialization. A measured implementation of the same indexing and links can then be composed with a verifier-to-CNF compiler, while preserving bounded occurrences and witness multiplicity. This package claims the checked bounded-occurrence reduction component. It does not claim a measured reduction on encoded words at this step or a general polynomial-time satisfiability algorithm.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
