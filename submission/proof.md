# Polynomial construction of all affine prefix queries

The theorem gives an actual polynomial-time word function that
constructs a batch of queries from an original NP input and a
full affine seed matrix. The seed word stores all coefficient
and bias bits in fixed-size consecutive rows. The query batch
uses the pinned unary-prefixed word pairing repeatedly. Each
prefix of the seed rows yields one query with the original
source input and that prefix's own encoded row list.

The first measured scanner splits the contiguous seed into
fixed-size rows. The next measured scanner traverses the row
list, appends each record to the current prefix, and emits the
corresponding query. The polynomial clock obtains the row
width from the source input's witness bound. Both scanners
include size-growth proofs on arbitrary raw states. Source
equations identify the actual machine's output with the list of
typed affine prefixes, including the order and number of queries.

The NP query verifier and original input witness bound remain
unchanged. A source no-input yields a batch containing no member
of the query language. For a source yes-input, at least one
eighth of the full typed seeds yield some query with just one
accepting bounded witness. The proof extends the successful
event from an existing good output width along the finite
product decomposition of the full seed. It does not need to
compute that width or count the original witnesses.
