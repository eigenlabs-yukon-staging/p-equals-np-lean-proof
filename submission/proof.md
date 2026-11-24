# Fixed-coin isolation with an encoded batch of 3-CNF formulas

For every language in the pinned class NP, the theorem constructs an
algorithm that receives an input and a word of coin bits, and emits a
serialized list of 3-CNF formulas. The algorithm is polynomial time in
the reference Turing-machine model. On valid tape lengths it emits the
reference encoding of each formula in order using the stated
length-prefixed list encoding. Every emitted formula has width at most
three. On inputs outside the language all formulas in the batch are
unsatisfiable for every tape of the prescribed length. On inputs in the
language at least one eighth of those tapes yield a batch with a formula
having exactly one assignment on its occurring variables.

The construction uses the earlier finite affine isolation and its
fixed-tape form. The witness-length polynomial p determines b = p(|x|).
Each bounded variable-length witness is represented injectively at
width 2b+1. The full matrix tape has 2b+3 rows with 2b+2 bits per row,
including one affine offset bit. A query is made at every nonempty
prefix width of this matrix. The probability argument supplies a width
at which a random prefix leaves exactly one accepted witness with
probability at least one eighth. Every tape contains the relevant
prefix, and the theorem counts tapes in the space of Boolean functions
on the common finite index set, with uniform measure expressed by
cardinality. The counting argument has no assumption that varying
prefixes are independent.

Each query word is passed to the parsimonious Cook–Levin compiler for
the measured affine-query verifier. A query's source input has length
at most the query-word length, so monotonicity of the original witness
polynomial bounds every accepted query witness by the polynomial in
the query-word length. This makes the bound in the compiler
correspondence exact for these accepted witnesses. The correspondence
preserves emptiness and uniqueness in both directions. In particular,
the one witness isolated among the source's valid witnesses is the
only accepted query witness, because the query verifier already
checks membership in that source set. On a negative input, the
existence of any satisfying formula would decode to an accepted
source witness, yielding a contradiction.

The measured algorithm first builds the query batch and then maps
the measured 3-CNF compiler over its serialized records. The proof
transfers the lower bound on isolation by inclusion between finite
sets of tapes. It requires no enumeration of witnesses or satisfying
assignments in either measured algorithm. The result is a randomized
reduction specifying what is true for each tape and how many tapes
succeed on positive inputs. No polynomial-time decider for the promise
target or deterministic collapse is claimed. All helper modules and
the separate P subset NP check are included for pinned-source replay.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
