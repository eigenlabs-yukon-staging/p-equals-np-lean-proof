# Measured product-budget branching over a Horn base

This package generalizes measured mixed-radix branching from a single fixed class of short clauses to any polynomial-time decidable clause family with a suitable satisfiability solver. In the concrete application, the base consists of all Horn clauses of the input formula. The exceptional clauses can have arbitrary width. The exact language is in the pinned P class when the product of widths of the non-Horn clauses fits a polynomial budget evaluated on the original encoding length.

## A reusable measured partition

`MeasuredCNFPartition` accepts a measured Boolean predicate on raw clause encodings. The resulting machine reads an ordinary canonical CNF and returns two self-delimiting fields. The first contains the reverse of the canonical list of clauses that pass the test, and the second contains the reverse list of those that fail it. A single step separates the next clause, evaluates the predicate on that clause, and prepends its encoding to the appropriate field. Empty remaining input is a fixed state.

The splitter supplies an exact length reassembly identity on every raw input. The identified clause length is therefore paid for by the decrease in the remaining field as the step prepends disjoint raw code. Pairing may add at most two delimiter symbols even on arbitrary raw states, so the reference constant-growth iteration applies. The canonical correctness proof is an induction over the number of clauses. Each clause has at least its delimiter and the raw input length is enough rounds. This establishes a reusable measured structure transformation independently of the base solver.

## Abstract branching theorem

`ClausePartitionProductSAT` assumes a measured clause predicate, a language in the pinned P class which agrees with satisfiability on every canonical formula all of whose clauses pass that predicate, and the property that clauses of size at most one pass. The machine keeps the passing part as the base. It enumerates a polynomially clocked list of mixed-radix indices for the failing part. For each index the prior measured branch generator emits one unit for each exceptional clause, or an empty clause if an index is invalid for that clause. It appends these units to the passing base and tests membership in the supplied P solver language.

The base-solver hypothesis is used only on canonical inputs that meet its required clause predicate. The original base passes by construction. The added branch clauses pass by the size-at-most-one assumption, including an empty clause that makes its branch unsatisfiable. Thus soundness uses the supplied solver's actual exact behavior on this domain. A satisfying assignment of a branch satisfies the base and the original exceptional clauses. Completeness uses the mixed-radix theorem to construct an index below the product of the exceptional widths from any satisfying assignment, and the clock premise ensures the search reaches it.

`ExactClausePartitionProductSAT` adds measured guards. It checks canonical syntax and computes the product of the exceptional clause widths clipped at one more than the polynomial budget. The clipped value fits in the budget exactly when the true product fits. The passing and failing lists may be reversed without affecting satisfaction or the width product. Intersecting the guards with the measured branch language therefore gives exact equality on all raw input words, including malformed and out-of-budget inputs.

## Horn specialization

`ExactHornProductSAT` chooses the exact measured Horn syntax guard as its clause test by applying it to a single encoded clause. Canonical encoding injectivity proves that acceptance of this singleton encoding is equivalent to having at most one positive occurrence. Empty clauses and all unit clauses pass. The base solver is the least-model measured Horn procedure, which runs on all canonical Horn formulae in the reference encoding. The generic construction combines the two to establish exact P membership on satisfiable formulae whose non-Horn width product fits the chosen polynomial.

This family includes arbitrary-width Horn bases and supports an input-dependent number of non-Horn clauses when their total product is small. The proof makes no assertion that all reference SAT inputs satisfy this budget or reduce to the resulting language. It demonstrates a checked composition of a reusable exception handling scheme and a measured tractable base.

## Verification and lineage

The reference is brilliant-hq/pequalnp-proofs revision `a9ad395e8fab5537a9017734c14360773f375cd8`, Lean v4.36.0, and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. With Node.js installed, prepare the reference using `lake exe cache get` in its Lean directory, then run `python3 check.py --reference /path/to/reference` from the archive. The replay overlays only the named Lean sources and supplies the exact statement bytes to the unchanged reference checker. Local replay digests identify the exact archive inputs and the checker dependency manifests.

The width-product package `202dd845-0798-4c0a-b30f-1448c78508b9` supplies the measured indexed mixed-radix units, unary division, and clipped width-product computation used directly by the abstract theorem. The canonical Horn package `70bf51af-ccb9-4a99-9616-faaec5dc05c1` supplies the measured Horn solver and exact syntax guard used in the application. The original indexed projection also remains in the archive and is invoked directly by the new abstract branching proof. Its source is from `5773f07e-e9f3-4db5-a12e-28b413a7f5c5`. The pinned reference machine operations and exact mathematical definitions are unchanged.

The standard Yukon local finalizer still needs the experiment and review artifacts and the workstation account cannot connect to its Docker socket. The network-isolated hosted Python experiment compares archive identity against the exact replay inputs and reports zero Lean kernel runs absent the reference environment. The local exact replay is the mathematical evidence. The candidate supplies no claimed numeric score.

Exact checker input and dependency digests match all eighteen archived statements. The pinned checker accepted the four new targets and rechecked 3,033 constants for partitioning, 4,206 for the generic branch theorem, 4,230 for the exact generic theorem, and 4,485 for the Horn specialization. Its transitive axiom reports were limited to `propext`, `Quot.sound`, and `Classical.choice`. The record retains the prior exact checks for unchanged modules.
