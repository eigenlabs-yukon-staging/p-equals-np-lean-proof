# A measured word-level machine for one sparse-image pruning round

The theorem constructs a word-level transducer that takes a pivot and an encoded list of candidate and image pairs. It returns an encoded list of the surviving candidates. The statement specifies the list encoding recursively, specifies how each candidate and image are paired, and proves the output agrees with the constructive deletion rule. The output is a sublist of the original pivot and candidates, shorter by exactly one occurrence. Under the finite sparse disjunction-image hypothesis, the output contains a YES candidate exactly when the original list does.

The transducer retains a flag, unprocessed records, and accumulated output. While it has not deleted a record, it compares the head record's image with every remaining image. For each comparison it parses the candidate-image pair and compares complete words. A measured record scan checks that every remaining image differs. If it discovers a repeated image, the worker omits the current candidate and sets the flag. This still lets the worker append all later candidates without further deletions.

At the end, the flag determines the treatment of the pivot. When a nonpivot record was dropped, the pivot is prepended to the encoded output. When there was no repeated image, the pivot is omitted. The proof identifies this behavior with the list deletion function for each well-formed encoded input, including an empty list of nonpivot candidates. The nonempty-list step is proved by the exact round-trip laws for pair decoding, and iteration up to the raw list length suffices because each serialized record consumes at least one symbol. When the unprocessed field becomes empty the state is stable, so extra clock rounds leave the answer unchanged.

The measured worker uses a constant additive step bound. The unprocessed field shrinks when its head is processed. Parsing an encoded head yields a candidate whose serialized contribution is bounded by the space in that record. Dropping a record adds at most the fixed flag overhead. This produces a pinned polynomial-time iteration on arbitrary raw words, including malformed encodings. The semantic pruning and preservation claims refer to the canonical input representation specified by the theorem.

Finite correctness then follows from the earlier collision argument. In the collision case the earlier candidate has a matching image with a surviving candidate. In the collision-free case the pivot being YES would imply too many distinct images in the finite set. Neither case requires a decider for the source predicate or target set. The machine takes precomputed image records. Attaching a polynomial-time image computation and iterating the bound after expansion are additional steps. No assumption that an actual sparse target is NP-hard is discharged by this theorem.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
