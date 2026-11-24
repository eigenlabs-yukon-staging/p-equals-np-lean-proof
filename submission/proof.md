The new target constructs one deterministic polynomial-time function on the pinned Boolean word representation of CNF. On every encoded formula with at most three literal slots in each clause and at most three total occurrences of each variable, it produces the encoding of a formula whose clauses each have exactly three distinct variable names. Every output variable occurs at most four times. Input and output are equisatisfiable. Both structural conclusions concern the typed formula whose encoding is exactly the machine output.

The reduction first discards tautological clauses. Within a remaining clause it removes duplicate signed literals. The proof relates this normalization to the original evaluator and bounds every variable's occurrence count by a sublist argument. In a clause without opposite polarities of the same variable, duplicate removal leaves distinct variable names. Old variable IDs are renamed by doubling them. Fresh IDs are odd and are confined to disjoint arithmetic blocks, twelve possible local positions per retained clause. For each vacant slot the reduction inserts a fresh positive literal and an independent copy of a five-clause forcing gadget. Each gadget has four distinct variable IDs and each clause has exactly three distinct IDs. A kernel-checked truth table proves that the terminal is false in every satisfying assignment and that the all-false assignment satisfies the gadget. The terminal has three gadget occurrences and gains one occurrence in its padded clause. Each internal variable stays within four occurrences. The proof checks this local counting bound for zero through three copies and establishes disjointness between the successive clause blocks.

A source assignment extends to the even names and to false at the odd names. The extension satisfies all output clauses whenever the original assignment satisfies all input clauses. Conversely, a satisfying assignment to the output forces every inserted literal to be false. Its even-name restriction then satisfies every retained normalized clause, and the discarded clauses were tautologies. The gadget can have multiple satisfying assignments, so the theorem asserts equivalence of existence of models.

The measured bit-word machine processes up to three raw literal encodings followed by a clause terminator and uses fixed fourth-slot consumption inherited from the bounded clause scanner. It detects opposite polarity by equal variable code tails and distinct full literal words. For a non-tautological clause, pairwise comparisons retain the last copy of each repeated word. The machine emits these literals under the even-name map, appends the computed padding, and appends the associated fixed gadget templates. The fresh base is a binary counter advancing by twelve only for retained clauses. A direct induction over typed clauses identifies the exact emitted encoding with the normalized, padded formula. Empty formulas, empty clauses, and tautological clauses each have explicit cases.

For arbitrary bit words the step consumes at least one bit when its input component is nonempty, and its index component grows by at most twelve bits. The nonincreasing measure depends on twelve times the remaining input length plus the binary base length. It bounds the increase in packed state length. The pinned polynomial iteration theorem, composed with the measured packing and projection, yields the actual polynomial-time transducer. This conclusion depends on the measured state and growth proof, beyond the pure equisatisfiability of the gadget construction.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
