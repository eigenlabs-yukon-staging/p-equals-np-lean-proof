# Repeated pruning to a unary frontier bound

The statement supplies a pinned word transducer for any measured map f on two candidate words. Its input is a unary cap word and a recursively serialized list of candidate words. If a finite set S has fewer members than the cap, and the image f of each candidate pair belongs to S exactly when one of the two candidates satisfies a predicate G, the result represents a sublist of the input with at most the cap number of records. Existence of a G candidate is preserved. The conclusion applies to any predicate G and any set S meeting the hypotheses for the input, and neither appears as a computational input.

The worker freezes a unary cap and tests whether there are more records than it permits by dropping one encoded record per unary tick. If enough records remain, it treats the head as the pivot. The worker attaches a copy of that pivot to each remaining record, uses the supplied measured map on each pair, and forms a serialized list of candidate-image pairs. Each record carries the original candidate alongside its newly computed image. A previously checked measured subroutine compares the images and removes either a nonpivot member of a collision or the pivot if all compared images are distinct. The sparse-cardinality argument uses the strict inequality of the set's size with the provided cap. Whenever the list has more than the cap number of records, its nonpivot list has at least cap positions.

The measured mapping construction is a reusable record flat-map, built using the pinned polynomial-time indexed range loop. A worker selects the indicated record by successive pair decoding and emits its transformed result. Padding in the reference range loop bounds the size of one transformation. The canonical encoding has enough raw symbols to index every real record, and indices beyond the last record contribute empty output. Correctness identifies the concatenation with the exact transformed list.

The pruning loop retains only its candidate serialization and cap between rounds. To bound growth even on malformed states it truncates the computed next list to the current list's raw length. In a well-formed round the result is a sublist; its serialization cannot be longer than the input, so this cap leaves it unchanged. Each nontrivial step removes exactly one record. The loop takes the raw serialized length as a sufficient clock because every actual record is represented by at least one bit. Once at or below the quota the loop remains stable.

The proof separately tracks sublist containment, iteration size, and the preserved existential predicate. A sublist inherits the hypothesis about the image map for every pair, so the same reasoning repeats at every round. This module makes no hypothesis about how the input candidate list was constructed and supplies no terminal decision test for G. It provides the repeated bounded-width step used by a separate layered search theorem.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
