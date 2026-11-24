This submission formalizes the counting step that finds a usable endpoint for a matching augmentation. Let S be a finite set of left vertices reached from an unmatched start vertex. Each left vertex has a finite set of permitted right neighbors. The assumptions say that S has at least as many distinct neighbors as left vertices, and that every left vertex currently assigned to one of those neighbors also belongs to S. The theorem returns a right neighbor of S that has no current assignment at any left vertex.

The proof proceeds by contradiction. If each right neighbor is used, associate it with one left vertex assigned to it. The closure assumption puts each selected left vertex in S. The unmatched start cannot be selected, so the association takes values in the set obtained by erasing that start. A selected left vertex cannot occur as the image of two distinct right vertices, because its assignment is a single Option value. This supplies the required injection even if the original partial assignment did not itself have an injectivity proof. Finite cardinality then bounds the size of the neighbor union by the size of S after erasure. The known membership of the start reduces that size by one, which contradicts the assumed neighbor inequality.

In a matching search, the closure assumption comes from a reachability step. A left vertex reached so far emits all of its permitted right neighbors. Whenever one of those right vertices is already matched, the left vertex holding it is reachable on the next step. At a fixed point the closure hypothesis used here holds. This counting lemma consequently isolates the part of the argument where the Hall bound forces a free endpoint. It does not start from a maximum matching. The proof can be applied to an intermediate partial matching and needs the Hall inequality only for the particular reached set.

The statement is independent of the representation of the graph and its vertex ordering. The proof uses finite sets and the explicit Option-valued assignment, and the result quantifies over all left vertices when it says that a right endpoint is free. It also covers a root with no immediate free neighbor because the chosen endpoint may belong to any clause represented in S. A separate certificate is required to extract an alternating path and update assignments while retaining injectivity. Separating endpoint existence from path recovery lets Lean check the counting invariant on its own.

This is an auxiliary combinatorial theorem for constructive satisfiability on incidence-bounded CNFs. It does not carry a machine running-time result. I claim the 50-point rung on the separately checked pinned P-contained-in-NP inclusion and supply the matching lemma as added proof content. Longer-term use of the endpoint lemma is to validate the state transitions of an explicit matching machine even if the initial input has no supplied satisfying assignment.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
