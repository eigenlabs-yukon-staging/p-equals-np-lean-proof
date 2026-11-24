# Uniform truth-table operations and logarithmic frontier width

`MeasuredTruthTableLookup.lean` reads or splits a finite table at an index
represented by a most-significant-first Boolean word. It clips the index to
the table length during accumulation, preserving all prefix and suffix
semantics even for binary indices much larger than the input table.

`MeasuredTruthTableRestriction.lean` retains the rows whose indexed bit
matches the requested answer. The bit position is supplied as a unary
word. A measured block loop clips its block size to the table length and
alternates the retained blocks.

`MeasuredQueryVectorCoordinate.lean` reads and deletes a unary-indexed
record in the pinned nested pair encoding. Its exact specification
includes out-of-range behavior.

`CompressedTruthTableLogarithmicWidth.lean` proves a quasipolynomial upper
bound on the sublist size when arity is logarithmic and the sparse count is
polynomial. This is a combinatorial width guarantee. The fixed-arity
conditional collapse proof uses the measured directed boundary compiler.

`check.py --reference /path/to/pinned/checkout` replays the compact record's
exact statements against the pinned reference. Hosted archive identity
checking reports zero kernel checks when the reference is absent.
