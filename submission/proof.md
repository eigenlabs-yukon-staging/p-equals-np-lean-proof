# A measured, parsimonious transformation from 4-CNF to 3-CNF

The theorem supplies a function on serialized words that is polynomial-time
computable under the pinned Turing-machine definition. On the reference
encoding of any 4-CNF, its output is the reference encoding of a 3-CNF.
The theorem provides a bijection between satisfying assignments to the
variables occurring in the two formulas. The index domains are finite
because they are obtained from the lists of literal occurrences. Assignment
values outside each domain default to false only when applying the
reference evaluator. An unsatisfiable input consequently has no output
models, and repeated literal occurrences do not add free choices.

In the output, each original variable number i becomes the even number
2i. A clause of width zero, one, two, or three remains a clause after this
renaming. For a width-four clause with literals a, b, c, d and zero-based
position j, the number 2j+1 names a fresh variable r. The clauses
(a or b or not r), (not a or r), and (not b or r) define r to be the
disjunction of a and b. The remaining clause (r or c or d) enforces the
original clause. Every original variable still occurs after renaming.
Distinct width-four positions have distinct auxiliary variables, including
when two input clauses are syntactically identical. Each satisfying
assignment on the original variables uniquely fixes all the auxiliary
values. The reverse map discards those values and recovers the original
assignment coordinate by coordinate. The proof covers empty formulas,
empty clauses, repeated variables, and both literal polarities.

The measured implementation scans the original pair encoding. It reads at
most four literal items before consuming a clause delimiter, carries the
binary position of the current clause, and emits the corresponding output
block. It doubles a nonzero variable by inserting one zero bit at the
front of its least-significant-first digit sequence. The code of variable
zero retains its empty digit sequence. The auxiliary literal inserts a
leading one bit in the clause-position digits. The state contains the
remaining input, the clause index, and the output so far. Each active
iteration shortens the remaining input and increases the index word by
at most one bit. Thus the sum of the remaining input length and the
index-word length is nonincreasing, including on malformed encodings.
The block length is linear in that measure. The resulting polynomial-time
bound is obtained from the reference measured iteration theorem, and
the exact serialized equation is proved separately by induction over
the source clauses.

The 3-CNF transformation preserves the number of satisfying assignments
and is reusable after a parsimonious reduction to 4-CNF. The proof does
not implement a SAT decision algorithm or a model counter. The package
contains the exact Lean target, the machine proof, its semantic refinement
and model equivalence, the complete pinned proof dependencies, and the
separate checked P subset NP target.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
