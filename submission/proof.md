# Removing a candidate by a collision or a sparse-image bound

The exact theorem describes a list of candidates, a distinguished pivot, and an image for each nonpivot candidate. It constructs one function that removes exactly one occurrence and whose output is a sublist of the original candidate list. The correctness hypothesis concerns any source predicate G and any finite set S of target images. An image is in S exactly when the pivot or the corresponding nonpivot candidate satisfies G. If S has fewer members than the nonpivot list has positions, the function preserves whether at least one original candidate satisfies G.

The pruning function uses equality on the images. It scans the image records for a pair of equal images, checking each current image against the tail. If it finds such a pair, it removes the earlier candidate but keeps the pivot and the later record. Equal images have the same membership in S. While the pivot satisfies G the list still has a YES candidate regardless of which nonpivot was removed. When the pivot fails G, the hypothesis identifies the two candidates' G values with the same membership value, so retaining the later candidate suffices. This reasoning works with repeated candidates and does not assume the original list is a set.

If the scan finds no collision, the list of images is duplicate-free. If the pivot satisfied G, every listed image would belong to S, contrary to its cardinality bound. The function therefore removes the pivot and preserves all remaining candidates. The proof makes no membership queries to S or tests of G. Those appear only in the correctness theorem. The computed transformation depends on the ordered records and decidable equality of their images.

The selected list order is preserved. A successful recursive collision search prepends the records that came before the removed occurrence and leaves the suffix in place. This gives the exact sublist theorem and proves the output is shorter by one. The list size can count positions even if some candidate words repeat, because the collision-free branch uses duplicate-freeness of the images, established over those positions. The failing collision search is linked to duplicate-freeness by a separate induction.

This is the combinatorial pruning step used in a sparse-hardness argument. Iterating it after a branching expansion can maintain a small frontier while preserving a YES branch, provided the disjunction images are computed and their lengths stay within the range of the sparse cardinality bound. This submission has a constructive list function but no complexity claim about the pinned bit-word encoding. The transducer, repeated pruning loop, and sparse language application have separate implementation and proof obligations. The target is a checked supporting bridge toward those obligations, not a proof that an NP-hard sparse language exists.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
