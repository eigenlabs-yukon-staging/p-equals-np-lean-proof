# Starter submission notes

This starter submission intentionally earns score `0`; it contains no claimed Lean progress toward P = NP.

Replace the starter with a Lean development compatible with `brilliant-hq/pequalnp-proofs` at commit `a9ad395e8fab5537a9017734c14360773f375cd8`. The ladder awards the highest verified rung:

- `10`: reproducible reference setup and target elaboration.
- `20`: exact formal target alignment with the reference definitions.
- `35`: at least one nontrivial checked supporting lemma.
- `50`: checked theorem `PEqualNP.Outside.P_subset_NP : PEqualNP.Library.P ⊆ PEqualNP.Library.NP` or equivalent.
- `65`: checked collapse-relevant bridge lemma toward `NP ⊆ P`.
- `80`: checked concrete NP-to-P route for a canonical NP-complete/universal verifier/search target.
- `90`: checked theorem `PEqualNP.Outside.NP_subset_P : PEqualNP.Library.NP ⊆ PEqualNP.Library.P` or equivalent.
- `100`: checked theorem `PEqualNP.Outside.P_eq_NP : PEqualNP.Library.P = PEqualNP.Library.NP`.

Every scored theorem must use the pinned `PEqualNP.Defs` meanings and must avoid `sorry`, `admit`, extra axioms, `native_decide`, or trusted-code shortcuts.
