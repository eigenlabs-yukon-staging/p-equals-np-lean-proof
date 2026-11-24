# Parsimonious Cook–Levin reduction to 3-CNF

For every polynomial-time Boolean verifier on input and witness and every
polynomial upper bound on witness length, the submitted theorem constructs
a polynomial-time map to encoded 3-CNF. For each input, Lean checks an
equivalence of types between its accepting witnesses of bounded length
and the satisfying assignments of the emitted formula. A witness is a
list of Boolean values, with length counted in the witness identity. A
satisfying assignment is a function on the finite set of variable
numbers appearing in the formula. The reference evaluator reads the
extension of that function which defaults to false outside those
variables. Empty sets of accepted witnesses correspond to empty sets of
models under this definition.

The first compiler follows the pinned Cook–Levin proof. It fixes the
verifier, numbers the machine configuration components, and builds a
run tableau whose length is bounded by a polynomial in the input length.
At every time and for every machine component, pairwise negative clauses
exclude two distinct values from simultaneously being true. The ordinary
tableau supplies the actual values for an accepting run. A satisfying
assignment therefore agrees with the deterministic run reconstructed
from its initial witness cells. A scan of the initial witness region
sees distinct positive symbols for false and true until a blank, and the
remaining witness entries are blank. A separate variable-support proof
covers the initialization unit clauses that mention trailing blanks
outside the bounded time-and-cell domain. Those extra variables are
forced by unit clauses. The resulting model type is equivalent to the
accepted witness type and the formula has width at most four.

The second compiler changes all existing indices to even numbers.
For each width-four clause at position j it introduces one odd-indexed
variable 2j+1, asserted to equal the disjunction of the first two literals.
It adds a width-three clause using that variable and the remaining two
literals. Each canonical valuation on the original variables fixes the
auxiliary variables uniquely. The proof checks that every old variable
still occurs after renaming and that all new occurring variables are
among the defining auxiliaries. This establishes an exact equivalence
between the finite model types of the 4-CNF and 3-CNF. The generator
implements the transformation directly on serialized literals. A measured
iteration consumes the input and accumulates the output with a growth
bound linear in the current measure.

The final proof composes the two measured word functions and the two
finite model equivalences. The intermediate models are used only to
prove the correspondence. The operation executed on words simply
produces the encoded formula. No loop enumerates satisfying assignments
or evaluates the verifier over the space of candidate witnesses. The
conclusion supplies a reduction and a witness-count preservation theorem.
It does not supply a deterministic polynomial-time SAT decider, a
counting algorithm, or a collapse of complexity classes. The included
reference P subset NP theorem is a separately checked target.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
