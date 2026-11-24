# Sparse complement images and early YES detection

The exact theorem constructs a list transformation depending on an image-size cap and an ordered list of candidate-image pairs. The operation either reports a YES certificate or returns a sublist of candidate words. Its correctness hypothesis says a pair's image belongs to a finite set S exactly when its candidate does not satisfy the predicate G. The set cardinality is at most the given cap. This hypothesis abstracts a reduction from the complement of a decision problem to a sparse target.

If the input list already has at most the cap number of entries, the transformation returns its candidate projection. For an oversized input, it checks equality among the images by scanning the ordered records. If a repeated image appears, it deletes the earlier of the two corresponding records and leaves all other records in order. The equal image membership gives the same value of G for both candidates. In particular, if the deleted record had a candidate satisfying G, the surviving equal-image record also has one. This establishes both directions of the existential preservation theorem without requiring any decision procedure for G.

If the input is oversized and no collision occurs, all its images are pairwise distinct. Suppose there were no G candidate. Every image would then belong to S by the complement-image hypothesis. A duplicate-free list of that length induces a finite subset of S of exactly the same cardinality, contradicting the cap. Thus the result may report a certified YES without producing a specific successful candidate. In a layered decision search this branch allows the machine to return true immediately. The proof of the YES claim is classical but the operation itself only examines the length and equality of the supplied image records.

The theorem gives separate equations for the Option result. A return of none proves an original candidate satisfies G. A return of some list gives sublist containment, the length upper bound by the maximum of the cap and one less than the original length, and preservation of existence of a successful candidate. The explicit result equations keep the intended statement entirely in the pinned checker language without relying on a generated match helper. No scoring claim depends on the earlier scratch statement whose match elaboration required such a helper.

This is a different decision mechanism from the pivot-based sparse disjunction rule. The image here depends on one original candidate, the finite set corresponds to the complement, and overflow certifies YES rather than identifying a candidate that can safely be discarded. The present theorem is the finite algorithmic core. A measured machine, repeated pruning, and final conditional sparse coNP-hardness implication still require additional proof. No sparse hard language is asserted to exist.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
