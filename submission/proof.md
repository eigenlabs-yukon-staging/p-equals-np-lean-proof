# Sparse coordinate patterns as a measured verifier

This submission turns deterministic finite coordinate isolation into a verifier in the pinned Lean machine model. Its input is an encoded source word and a serialized pattern. Its witness is an ordinary source verifier witness, with no extra witness for correctness of the pattern. The exact theorem supplies the polynomial-time Boolean machine, proves the induced query language belongs to NP, relates the finite witness set to the original relation and length bound, and proves a singleton query exists for every selected witness when the set has at most c+1 members.

Each pattern consists of c slots. A blank slot accepts any word, and a populated slot requests a bit value at a unary coordinate index. The witness is mapped to a fixed-length encoding of 2b+1 bits, where b is the original bound evaluated at the source length. The length prefix distinguishes bounded witnesses that differ only by a trailing zero or by their length. The machine for a populated slot selects from this encoding with a bounded list operation and compares the selected bit. A record scanner combines the checks with conjunction. Its clock and state size bounds apply to encoded input words including malformed records. The singleton property uses the exact round trip for canonical pattern records and the checked semantics of the fixed-length witness encoding.

The verifier also checks that the witness length is at most p evaluated at the original source length and that the original Boolean decider accepts the original source and witness. Every accepting witness for an encoded source and any pattern code therefore belongs to the original finite witness set. This property holds on the queries that do not isolate a unique witness, and will provide unconditional soundness for a future query enumeration on source NO instances.

The NP certificate is the source witness itself. The source extracted from the query has length at most the query length. Monotonicity of natural-coefficient polynomials makes the source witness guard imply the polynomial certificate bound required by the pinned NP definition when it is evaluated at the longer query. The machine's explicit guard retains the smaller bound. The membership proof thus works with the exact word-level encoding used by the theorem.

The finite isolation argument applies the proved coordinate separation lemma to the injective fixed-length encoding of the feasible witnesses. Copying the coordinates of a selected witness into the pattern leaves exactly that witness, and the spare slots can remain blank. The theorem does not assume that all NP problems admit constant witness multiplicity. Its local statement quantifies over the actual cardinality of the witness set at the source input. The separate polynomial query batch step uses a globally fixed c to keep finite pattern enumeration polynomial. This submission establishes the verifier and singleton property before any oracle call or classification of the source language.

## Reproduction

After preparing the pinned reference checkout, run the following commands
from this submission directory. Use a checkout with the Lean toolchain
and Mathlib prepared and put Node and Lake on PATH.

```sh
python3 check.py --overlay /absolute/path/to/reference
export PEQUALNP_REFERENCE_ROOT=/absolute/path/to/reference
printf '%s\n' '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' | python3 check.py
```
