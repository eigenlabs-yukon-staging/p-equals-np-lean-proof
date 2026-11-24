# A measured bounded-frontier search under sparse disjunction reductions

Fix a language G, a sparse target language A, and a measured reduction taking two words to a word in A exactly when at least one original word lies in G. The theorem supplies a deterministic polynomial-time decider for G under explicit layered-search assumptions. Each candidate has a measured list of children, its G membership agrees with existential membership of the children, and each child grows in word length by at most a fixed constant. The layer count is polynomial. A supplied measured leaf test must agree with G on nodes at that layer of the full unpruned expansion.

The worker expands a serialized candidate list using a generic measured flat-map over records. It repeatedly shrinks the expansion with the measured sparse-image rule. For an overfull candidate list, select a pivot, evaluate the disjunction reduction on the pivot and every remaining candidate, and compare the resulting image words. A duplicate permits deletion of one equal-image record. If the images are all distinct, the pivot being in G would put too many images in the sparse set, so the pivot can be deleted. The machine never tests membership in the sparse set. The finite set occurs in the correctness proof.

Every candidate at layer n has length bounded by the input length plus n times the per-layer increase. The resulting global length bound is polynomial. Apply the output-length bound for the measured reduction to the encoded pair of two words within that limit to get a polynomial bound on all target image lengths. Cumulative sparsity applies at that length. The worker uses one more than the corresponding sparse count bound as its frontier cap. A second unary polynomial clock bounds the raw serialization length of any frontier with the allowed number and maximum size of records. For arbitrary machine states the output is cut to that cap, and the proof ensures that the cut has no effect on correctly reached states.

The layer invariant verifies three facts in the pinned representation. Every retained record fits the per-depth length bound. Every retained record at a given depth appears in the full expansion at that depth. Existence of a retained YES candidate is equivalent to the original word being in G. The first two follow from the expansion growth and the sublist property of pruning. The third combines preservation by expansion and preservation by every sparse prune. Therefore the final leaf test is accurate on the retained list and a measured Boolean list disjunction decides the original input.

The theorem quantifies over the branching mechanism and its test so the machine construction can be reused. The branching representation is the paired list encoding, specified recursively in the statement. The sparse target, reduction, growth, and terminal correctness remain explicit hypotheses. The application to NP uses the verifier-prefix search as an instance of these assumptions. This submission is the standalone measured simulation rather than a claim that any particular NP language has an unconditional sparse reduction.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
