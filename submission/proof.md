# A parsimonious Cook–Levin reduction for bounded verifier witnesses

The proposed milestone is a Lean theorem about the reference definition of
polynomial-time computability and the reference CNF encoder. Fix a total
polynomial-time Boolean verifier on an input and a witness, and fix an arbitrary
natural-coefficient polynomial witness-length bound. There is a polynomial-time
map from each input to encoded CNF whose satisfying assignments are in bijection
with the accepted witnesses of length at most the bound. The theorem treats
witnesses as Boolean lists, so lists of different lengths are distinct,
even when one is a prefix of the other. A model gives exactly one Boolean
value to each variable mentioned in the emitted formula. Variables outside
that set are set to false when invoking the reference CNF evaluator. The model
correspondence therefore preserves the number of solutions with the finite
assignment convention stated in the theorem.

The reference Cook–Levin tableau already has clauses asserting that each
variable on the true computation path is true. Those clauses permit other
variables in the same group to be true as well. The new construction adds a
negative binary clause for each unordered pair of distinct values in each
program-counter, state, or tape-cell group. The original induction supplies at
least one true value in each group, so satisfying assignments agree with the
canonical deterministic run throughout the bounded tableau. Completeness
checks the clauses on that canonical run. In the initialization region the
witness symbols are two distinguished positive symbols. The length cutoff is
the first blank, followed only by blanks. A length at the upper bound has no
blank in the witness region, and a length of zero puts blanks throughout it.

The support proof classifies every variable the resulting formula mentions.
Step and terminal clauses stay within the bounded groups. The initialization
can also mention blank cells beyond the bounded tableau because its trailing
blank range is offset by the input and witness lengths. The corresponding
unit clauses force their values. Every index used to distinguish witness
values occurs among the added clauses, since the reference bound leaves each
group at least two possible values. Consequently restricting canonical runs
to actual formula variables is injective, and every satisfying assignment
on those variables arises from a canonical accepting run. It is unnecessary
to count infinite total extensions or enlarge the counted model domain.

The machine proof builds the added clauses by measured loops for time and
cell position and fixed loops for the verifier's stack and alphabet sizes.
The literal blocks use the reference variable-number syntax directly. The
ordinary tableau encoding and the added clauses are concatenated by the
reference polynomial-time append construction. The verifier machine
simulation retains the input-stack validity invariant of the reference
compiler. Its time bound is composed with the sum of the input length and
witness-length polynomial, then scaled and shifted by the simulation
constant. Deterministic halting identifies the machine output with the
verifier bit in both directions. The source reuses the pinned simulation
proof and preserves the input-stack invariant in its existential result.

The theorem is a reduction from bounded verifier counting to counting
satisfying assignments. It does not supply a polynomial-time algorithm for
deciding SAT or for computing either count. It makes no assertion of a
complexity class equality or a lower bound. The artifact includes the Lean
statement, the replayable proof, the pinned source dependencies needed for
replay, and the separate reference P subset NP check.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
