The theorem provides an explicit five-clause gadget on four variables in the pinned CNF representation. Every clause contains exactly three literals on distinct variable names. Its terminal, variable zero, occurs in exactly three clauses. Each of the other three variables occurs in exactly four clauses. The all-false assignment satisfies the gadget. Every satisfying assignment gives false to the terminal. On the four supported names the gadget has exactly six satisfying assignments, so the terminal is forced even though its internal assignment is not unique.

The displayed clauses use the triples (zero, one, two), (zero, one, three), (zero, two, three), and twice (one, two, three), with signs recorded in the Lean source. If the terminal is true, the three clauses mentioning it reduce to binary constraints on the other names. Checking the eight possible internal triples shows that these constraints together with the two clauses without the terminal cannot all hold. The proof splits on the terminal Boolean and the three internal Booleans, and unfolds the pinned evaluators on each branch. No axiom describing the outcome of the finite search is used. The separate all-false check verifies the exhibited satisfying assignment directly.

The shape theorem includes the bound that all used names are less than four. A finite check on the source list establishes clause widths and distinctness of the projected names. The degree calculation uses the flattened list and its ordinary occurrence count after dropping signs, so it counts the terminal positions and the internal positions with their exact multiplicities. A further finite computation filters the full function space Fin 4 to Bool by the decoded CNF predicate and checks that the accepted set has cardinality six. The count only concerns the actually used names. Arbitrary values at all other natural numbers cannot change the formula evaluator.

One copy provides a way to pad a width-one or width-two clause with a positive literal on a fresh terminal that no satisfying model can use. The terminal then occurs one more time and reaches degree four. Other gadget names remain at degree four if each copy is independently fresh. An empty clause needs three such terminal literals and remains unsatisfiable, because all are forced false. This theorem verifies the local degree and truth requirements. Global fresh-name allocation, source normalization of repeated or opposite-signed names, equisatisfiability, and a measured encoding transducer are separate results. This proof claims no preservation of the number of models under gadget attachment, which is precisely why the accepted local count is included. The submission treats the gadget as a finite supporting result at the P-subset-NP inclusion rung.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
