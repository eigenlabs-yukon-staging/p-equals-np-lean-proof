# Proof note: `P ⊆ NP` and a conditional collapse bridge

## What is claimed, and what is not

**Rung attempted: 65** (collapse-relevant formal bridge). **Fallback rung: 50** (`P ⊆ NP`).

This submission does **not** prove `P = NP`, `NP ⊆ P`, or that any NP-complete language is in
P. Rungs 80, 90 and 100 are not attempted. The two bridge theorems below are conditional: their
hypothesis (some NP-hard language is in P) is left open.

| Theorem | File | Statement |
|---|---|---|
| `PEqualNP.Outside.P_subset_NP` | `lean/PEqualNP/Outside/P_subset_NP.lean` | `PEqualNP.Library.P ⊆ PEqualNP.Library.NP` |
| `PEqualNP.Outside.Collapse_of_NPHard_mem_P` | `lean/PEqualNP/Outside/Collapse_of_NPHard_mem_P.lean` | `∀ L : Language Bool, PEqualNP.Library.NPHard L → L ∈ PEqualNP.Library.P → PEqualNP.Library.NP ⊆ PEqualNP.Library.P` |
| `PEqualNP.Outside.Equality_of_NPHard_mem_P` | `lean/PEqualNP/Outside/Equality_of_NPHard_mem_P.lean` | `∀ L : Language Bool, PEqualNP.Library.NPHard L → L ∈ PEqualNP.Library.P → PEqualNP.Library.P = PEqualNP.Library.NP` |

`P`, `NP`, `NPHard`, `PolyTimeReducible` and `Language Bool` are the reference definitions in
`lean/PEqualNP/Defs/Base.lean` (and Mathlib). No file here declares anything but one theorem.

## Where the mathematics comes from

The substance is the reference project's own library, not new work of this submission. The
three `Outside` files are short terms over reference lemmas. To satisfy the rule that every
helper a scored theorem depends on is in the submitted source, the helper modules are included
as unchanged copies from `brilliant-hq/pequalnp-proofs` at commit
`a9ad395e8fab5537a9017734c14360773f375cd8` (Apache License 2.0, copyright of its authors):

| File under `lean/PEqualNP/` | Role |
|---|---|
| `Defs/Base.lean` | the definitions: machines by Mathlib's `Turing.FinTM2`, `P`, `NP`, `PolyTimeReducible`, `NPHard` |
| `Library/Machines/Run.lean`, `Compose.lean`, `ComposeRun.lean` | sequential composition of two `FinTM2` machines, with its polynomial time bound (`comp_polyTime`) |
| `Library/Machines/FilterMap.lean` | a one-pass filter-map machine is polynomial time (`filterMap_polyTime`) |
| `Library/L007.lean` | polynomial-time computable functions compose |
| `Library/L010.lean` | `P ⊆ NP` |
| `Library/L016.lean` | P is closed under polynomial-time many-one reductions |

`check.py` holds the git blob id of each of these at the reference commit and reports whether
the submitted bytes match.

## The arguments

**`P_subset_NP`** is `PEqualNP.Library.L010`. Given a decider `f` for `L`, take the relation
`R = {(x, w) | x ∈ L}` and the polynomial `0`. `R` is decided by `fun p => f p.1`: the pair
encoding `x.map Sum.inl ++ w.map Sum.inr` is projected to `x` by a filter-map machine
(`filterMap_polyTime`), then `f` runs (`L007`). The empty witness has length `≤ 0`.

**`Collapse_of_NPHard_mem_P`.** Let `L` be NP-hard and in P, and `L' ∈ NP`. NP-hardness gives
`PolyTimeReducible L' L`; `L016` (reduction, then decider, composed by `L007`) gives `L' ∈ P`.
The proof term is `fun L hhard hp L' hL' => L016 L' L (hhard L' hL') hp`.

**`Equality_of_NPHard_mem_P`.** `Set.Subset.antisymm` of `L010` and the argument above.

The bridge is the standard reason an NP-hardness result matters for the final inclusion: any
proof of `NP ⊆ P` that goes through one hard language would end with exactly this step. Its
formal content is machine composition with a polynomial bound (`Machines/Compose*.lean`,
about 30 KB of Lean), which Mathlib does not have. The reference lemma `L018` states a close
variant for NP-complete `L`; the versions here need only NP-hardness.

## Evidence

**Checked locally, with Lean.** The submitted files were laid over a clone of the reference
repository at the pinned commit (the eight reference files were byte-identical to the ones
already there; only the three `Outside` files were new) and the reference checker
`tools/check-lean.mjs` was run on each theorem with its statement, under Lean `v4.36.0` and the
pinned Mathlib. The verdict lines are in `local-check.md`. That file is a record of a run on
the author's machine: supporting context, not something the hosted run reproduces.

**Hosted run.** The hosted experiment sandbox is a Python-only container with no network and a
20 second budget, so it cannot run Lean. There `check.py` reports `lean_executed: false` and
`proof_ladder_points: 0` (the points that run itself verified), plus static checks: the
reference copies are unchanged, each `Outside` file declares exactly one theorem with the exact
statement, no `sorry`, `admit`, `axiom` or `native_decide` token occurs in any Lean file, and
every project import resolves to a submitted file (except the definitions root `PEqualNP.Defs`,
which `Machines/Run.lean` imports and the reference tree supplies; the statements use
`Defs/Base.lean` only).

**To reproduce the Lean check** (elan, Node.js 20+, git; about 6 GB for Mathlib):

    git clone https://github.com/brilliant-hq/pequalnp-proofs ref
    git -C ref checkout a9ad395e8fab5537a9017734c14360773f375cd8
    (cd ref/lean && lake exe cache get)
    echo '{"reference_commit":"a9ad395e8fab5537a9017734c14360773f375cd8","timeout_seconds":1200}' \
      | PEQUALNP_REFERENCE_ROOT=$PWD/ref python3 submission/check.py

## Limits a reviewer should weigh

- The theorems restate or lightly generalise lemmas the reference project already has. If the
  ladder is meant to reward only new mathematics, the fair reading is lower than 65.
- The submission is a patch over the reference tree, not a standalone Lake project: the full
  definitions root is 39 files and does not fit the submission limits.
- The hosted run cannot confirm the Lean verdicts; they rest on the local record and on a
  reviewer repeating the commands above.
