# Record of the local Lean check

This is a record of one run on the author's machine (macOS arm64, 2026-11-24). It is supporting
context only: the hosted run does not reproduce it. `proof.md` gives the commands to repeat it.

- Reference: `brilliant-hq/pequalnp-proofs` at `a9ad395e8fab5537a9017734c14360773f375cd8`
- Toolchain: `leanprover/lean4:v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (prebuilt cache)
- Checker: the reference clone's own `tools/check-lean.mjs` (check-lean 3), mode `check`
- Command: `PEQUALNP_REFERENCE_ROOT=<clone> python3 submission/check.py`; it reported `lean_executed: true`, `proof_ladder_points: 65`

Last line the checker printed for each theorem. The list of re-checked modules is shortened here
to the non-definition modules; the checker also re-checked the 39 modules of `PEqualNP.Defs`.

## `PEqualNP.Outside.P_subset_NP`

exit code 0

    ACCEPTED (check): PEqualNP.Outside.P_subset_NP; axioms [propext, Quot.sound, Classical.choice]; kernel re-checked 867 constants of [PEqualNP.Defs (39 modules), PEqualNP.Library.Machines.Run, PEqualNP.Library.Machines.Compose, PEqualNP.Library.Machines.ComposeRun, PEqualNP.Library.L007, PEqualNP.Library.Machines.FilterMap, PEqualNP.Library.L010, PEqualNP.Outside.P_subset_NP]

## `PEqualNP.Outside.Collapse_of_NPHard_mem_P`

exit code 0

    ACCEPTED (check): PEqualNP.Outside.Collapse_of_NPHard_mem_P; axioms [propext, Quot.sound, Classical.choice]; kernel re-checked 836 constants of [PEqualNP.Defs (39 modules), PEqualNP.Library.Machines.Run, PEqualNP.Library.Machines.Compose, PEqualNP.Library.Machines.ComposeRun, PEqualNP.Library.L007, PEqualNP.Library.L016, PEqualNP.Outside.Collapse_of_NPHard_mem_P]

## `PEqualNP.Outside.Equality_of_NPHard_mem_P`

exit code 0

    ACCEPTED (check): PEqualNP.Outside.Equality_of_NPHard_mem_P; axioms [propext, Quot.sound, Classical.choice]; kernel re-checked 870 constants of [PEqualNP.Defs (39 modules), PEqualNP.Library.Machines.Run, PEqualNP.Library.Machines.Compose, PEqualNP.Library.Machines.ComposeRun, PEqualNP.Library.L007, PEqualNP.Library.Machines.FilterMap, PEqualNP.Library.L010, PEqualNP.Library.L016, PEqualNP.Outside.Equality_of_NPHard_mem_P]
