# A measured parsimonious reduction to three literal occurrences per variable

The theorem gives a polynomial-time map on the reference binary
CNF encoding. Given a 3-CNF, the output is again a 3-CNF and every
variable number has at most three literal occurrences. The
conclusion gives a bijection of satisfying assignments on the
variables actually occurring in the input and output. The
assignment evaluator uses false outside those finite domains.

The transformation gives each literal occurrence a fresh index,
in the order of the serialized clauses and literals. It retains
the polarity and clause membership of that occurrence. For
every original variable it groups all of its fresh indices.
For a group of indices in order, the added binary clauses impose
an implication from each index to the next and from the last
to the first. A satisfying assignment to those clauses gives
the same truth value at every index of the group. If one
occurrence is true, the implications around the cycle force
every other occurrence true. If the group is entirely false
the implications are satisfied as well. A singleton group
uses a self implication. Both of its literals count as occurrences
in the displayed occurrence bound.

For completeness, an input model assigns each new variable the
value of the original variable at its occurrence. The renamed
clauses evaluate just as before, and every cycle is satisfied.
For soundness, a model of the output gives a common value for
each group and hence a valuation for every original variable.
The original formula evaluates as the renamed clauses do. The
two maps are inverse on the finite model domains. Each used
index has one occurrence in the renamed clauses and at most
one positive and one negative literal in its cycle clauses.
Those are all occurrences of that index.

The measured implementation reads each serialized literal and
clause terminator, carries a binary new-variable counter, and
emits the renamed formula along with a record list pairing
original names with the new indices. A second measured loop
examines suffixes of those records. It emits a cycle exactly
at the last occurrence of a name. To form that cycle it filters
the full occurrence list by the name and writes the implications
using the selected index words. The source establishes the
polynomial-time bound for the transducers and the exact
serialization agreement independently of the model argument.
The package includes the measured Lean theorem, its exact
statement, the source closure and the separate P subset NP check.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
