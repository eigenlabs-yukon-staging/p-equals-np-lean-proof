# P = NP Lean proof ladder

Create verifiable Lean 4 progress toward `PEqualNP.Library.P = PEqualNP.Library.NP`, read against the definitions and checker discipline of `brilliant-hq/pequalnp-proofs`.

Reference implementation: `https://github.com/brilliant-hq/pequalnp-proofs`, inspected at commit `a9ad395e8fab5537a9017734c14360773f375cd8`. The reference repository treats a result as checked only when the pinned Lean toolchain, pinned Mathlib, and checker accept it; it does not claim that P versus NP is settled.

A submission should provide a Lean development, preferably a fork-compatible copy or patch of the reference project. The final target is:

```lean
theorem PEqualNP.Outside.P_eq_NP : PEqualNP.Library.P = PEqualNP.Library.NP := by
  ...
```

Submissions may also earn credit for intermediate checked targets. Useful conventional names are:

```lean
theorem PEqualNP.Outside.P_subset_NP : PEqualNP.Library.P ⊆ PEqualNP.Library.NP := by
  ...

theorem PEqualNP.Outside.NP_subset_P : PEqualNP.Library.NP ⊆ PEqualNP.Library.P := by
  ...
```

## Scoring ladder

The score is one integer, `proof_ladder_points`, equal to the highest rung fully supported by reproducible Lean evidence. Award the highest applicable rung only; do not add rungs together.

| Points | Rung | What must be verified |
|---:|---|---|
| 0 | No accepted Lean progress | No submitted Lean evidence checks under the reference discipline, or the submission only contains prose/claims. |
| 10 | Reproducible reference setup | The submitted project uses the pinned `pequalnp-proofs` toolchain/Mathlib/checker discipline, the target statement elaborates against `PEqualNP.Defs`, and the run evidence is reproducible. |
| 20 | Exact formal target alignment | The submission states the intended targets using the reference definitions `PEqualNP.Library.P` and `PEqualNP.Library.NP`, with no local redefinitions, weakened claims, or changed imports. |
| 35 | Checked supporting lemma | At least one nontrivial supporting Lean lemma relevant to P/NP, reductions, verifiers, encodings, machines, or polynomial-time bounds is accepted by Lean with no `sorry`, `admit`, or extra axioms. |
| 50 | `P ⊆ NP` inclusion | A Lean theorem equivalent to `PEqualNP.Library.P ⊆ PEqualNP.Library.NP` checks under the reference definitions. |
| 65 | Collapse-relevant formal bridge | A substantial bridge lemma toward `NP ⊆ P` checks, such as a verified reduction/verifier/NP-completeness component or a reusable polynomial-time simulation lemma that the final inclusion could depend on. |
| 80 | Concrete NP-to-P route | A checkable Lean theorem establishes that a canonical NP-complete target or an explicitly stated universal verifier/search problem lies in `PEqualNP.Library.P`, under the reference definitions and with the needed polynomial-time bounds. |
| 90 | `NP ⊆ P` inclusion | A Lean theorem equivalent to `PEqualNP.Library.NP ⊆ PEqualNP.Library.P` checks under the reference definitions, even if the final equality theorem is not yet packaged. |
| 100 | Full target theorem | The exact theorem `PEqualNP.Outside.P_eq_NP : PEqualNP.Library.P = PEqualNP.Library.NP` is accepted under the reference checker discipline. |

A rung is valid only when all helper declarations it depends on are included in the submitted source and are themselves kernel-checkable under the same pinned toolchain. Partial attempts at a rung receive the previous fully verified rung.


## Validity requirements

Every scored rung must satisfy all of the following:

1. Statements are read against the pinned `PEqualNP.Defs` root, not locally redefined or weakened versions of P, NP, languages, reductions, verifiers, machines, encodings, or polynomial-time bounds.
2. Lean accepts the scored theorem(s) with no `sorry`, `admit`, synthetic placeholder, added axiom, `native_decide` escape, or other trusted-code shortcut.
3. The proof's transitive axioms are limited to the reference checker allowlist: `propext`, `Classical.choice`, and `Quot.sound`.
4. Helper declarations used by the scored theorem(s) are included in the submitted source and are themselves kernel-checkable under the same pinned toolchain and Mathlib.
5. The verifier can reproduce the check from the submitted files. Prose explanations, claimed terminal output, or untrusted score JSON are supporting context only, never sufficient by themselves.

Use the bundled `submission/check.py` as an executable harness sketch. It looks for pequalnp-style target theorem names and, when possible, runs the reference `tools/check-lean.mjs` checker for the exact final target. The LLM reviewer must still read the source and run evidence before assigning the ladder score.
