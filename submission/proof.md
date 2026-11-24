# Positive binary CNF minimum-weight decision is NP-complete

The target language accepts a paired word with an encoded CNF and
a budget word if the CNF contains only positive clauses of width
one or two and admits a satisfying assignment with twice its
true-name weight at most the budget word's length. The weight
counts distinct occurring variable names. The membership proof
uses the pinned bounded SAT verifier, a measured scan that checks
clause shape, a distinct-name weight counter, and the pinned
polynomial length comparator. Taking every second budget bit
turns the length into its floor half. Any semantic satisfying
assignment has a canonical reference witness with length at most
the CNF encoding.

The raw-word reduction builds an occurrence conflict graph.
A prepended anchor and one marker for each input clause are
forced true. Each literal occurrence receives a separate vertex
name. Each pair of inconsistent occurrences, or distinct
occurrences in the same clause, gives a positive binary clause.
Setting an occurrence vertex false selects it. A satisfying
target assignment selects a pairwise compatible family. For T
occurrences and M clauses, its true-name weight plus the selected
cardinality is T + M + 1. A budget of T + 1 therefore enforces a
selected occurrence from every clause.

The polynomial compiler uses measured word transducers. Source
item traversal emits vertex records with distinct serial codes,
row codes and the original literal codes. The second measured
scan visits each ordered pair of records and emits an edge when
the conflict flag fires. A clause-membership correspondence
relates the scanner output to the independently verified graph
construction after an injective renaming. The budget word has
length 2(T + 1). The reduction also maps malformed source
words to a fixed no-instance and composes with the pinned SAT
completeness reductions.

The archive contains all supporting source files byte for byte.
The supplied statement and source hashes reproduce the independent
kernel check at the pinned revision. The verification script
distinguishes actual Lean execution from a source-hash audit.

The source archive uses an XZ stream with a lossless identifier
table inside it. The checker restores each escaped identifier,
then parses the original path-to-source mapping. Base64 and
decimal records reconstruct the exact compressed stream.
