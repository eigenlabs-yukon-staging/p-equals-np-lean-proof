# Mahaney's theorem for pinned polynomial-time reductions

The checked theorem states that if a bit-word language A has polynomially many members up to each length and every pinned NP language admits a pinned polynomial-time many-one reduction to A, then the pinned language classes P and NP coincide. The hypotheses are explicit in the intended statement. Cumulative sparsity supplies for every length a finite set containing precisely the words of A up to that length, with cardinality bounded by a natural-coefficient polynomial evaluated at that length. The theorem requires no membership decider for A.

For each language L in NP, unpack its verifier relation and certificate-length polynomial. An extension language asks whether a given source and witness prefix admit a suffix whose concatenation satisfies the verifier and length guard. That extension language is in NP by the checked prefix verifier. A second checked construction recognizes paired disjunction of two extension inputs in NP: its certificate has a Boolean branch tag and a bounded witness for the selected side. The NP-hardness hypothesis gives a measured polynomial-time reduction from this paired disjunction to A. It supplies the images used in the pruning argument without deciding A.

A deterministic layered search maintains a serialized list of extension candidates. At a node whose current prefix is already a feasible witness, its only child is that same node. Other nodes produce the two prefixes formed by appending one bit to the current prefix. At every step, extension feasibility is equivalent to feasibility of at least one child. After the prescribed polynomial number of layers, testing the node's current prefix suffices. Any node whose prefix has never been feasible has grown by one bit per layer, so a feasible proper extension would exceed the cap. The proof follows this condition even on noncanonical raw inputs interpreted by the pinned parser.

The width bound comes from sparse collision pruning. Compare the reduced images of disjunctions of one pivot with the other candidates. An equal pair of images warrants discarding one nonpivot candidate. If there are too many distinct images to lie within the sparse set, the pivot cannot be feasible. The measured worker computes the reductions, checks collisions, and deletes candidates while keeping the YES condition. The reduction output-length polynomial and the bound on candidate growth determine the correct sparse length limit. The sparse counting polynomial then determines the frontier width, and those same bounds determine a cap on the serialized state. A truncation used to bound the machine on arbitrary words leaves each valid frontier intact.

Composition with the measured final leaf test gives the deterministic decider required by the pinned P definition. Initialize the extension input with the original word and the empty prefix to obtain a decider for L. The reverse inclusion uses the pinned P-subset-NP theorem. This is a conditional class equality of a standard structural kind. The development proves the consequence of the stated sparse hard-set hypothesis, and the existence of such a set remains a premise. Its score claim is the checked collapse-relevant bridge rung.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
