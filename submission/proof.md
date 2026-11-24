# Surjectivity of binary Hankel hashing against a nonzero vector

Fix an input dimension n, an output dimension k, and a nonzero vector
d of n entries in the two-element field. The new theorem proves that
every prescribed output vector b of length k can be realized by some
seed of n+k field entries. The value of coordinate i is the sum over
input coordinates j of the seed value at index i+j times d[j].
The matrix entries are constant on anti-diagonals. Reversing the
input coordinate order gives the corresponding diagonal-constant
Toeplitz form. The theorem uses a seed of length n+k to keep all
index bounds direct, so its last coordinate can be unused.

The proof selects the largest input coordinate p where d[p] is
nonzero. This coordinate exists because the hypothesis d is nonzero
is a statement about the whole vector and the input index set is
finite. The proof uses that a nonzero element of the two-element
field equals one. For every coordinate j strictly larger than p,
d[j] is zero. The induction builds an unbounded sequence and
satisfies one more output coordinate at every step. At stage i,
it adds the required correction to the sequence at position i+p.
That position appears with coefficient one in output coordinate i.
No other input coordinate contributes to that update in the i-th
row. An earlier row r<i could read that same position only in a
column j>p, whose coefficient is zero. Therefore the update
preserves all previously achieved outputs. After k updates the
sequence is restricted to the finite seed domain.

The proof separates existence of a finite pivot from the inductive
equations. It covers output dimension zero because the base case
contains no equations. Input dimension zero is ruled out by the
nonzero-vector hypothesis. There is no matrix inversion oracle,
arbitrary field extension, or informal use of random initialization.
The verification uses the exact finite sum and index arithmetic
shown in the statement. The bound proofs in the public statement
are explicit natural-number inequalities, allowing the pinned
checker to elaborate the statement without a local helper constant.

This is a reusable algebraic step for pairwise-independent hashing
with short seeds. One can apply it to the difference of two distinct
inputs. Together with affine offsets and a fibre-counting result,
surjectivity gives the joint output cardinalities needed for
witness isolation. The present theorem states the surjectivity
component and does not claim a measured hashed verifier, a full
randomized reduction, or a deterministic SAT algorithm. The package
contains the Lean target and the pinned-project sources needed for
independent replay, together with the separate P subset NP check.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
