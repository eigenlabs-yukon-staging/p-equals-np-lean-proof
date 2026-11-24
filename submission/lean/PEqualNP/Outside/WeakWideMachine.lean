import PEqualNP.Outside.BackdoorPathCore
import PEqualNP.Outside.BackdoorSearchFacts
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Outside.WideBackdoorBranch
import PEqualNP.Outside.WideClauseChoice

namespace PEqualNP.Outside.WeakWideMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.BackdoorPathCore
open PEqualNP.Outside.FirstWideCollector (gather gather_cpt)
open PEqualNP.Outside.FirstWideClause (firstWide firstWide_some names_ne_nil gather_enc)
open PEqualNP.Outside.WideClauseChoice (choose choose_cpt choose_member)
open PEqualNP.Outside.BackdoorSearchFacts (vcode_bound)
open PEqualNP.Outside.WideBackdoorBranch (mem_residual)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers
open PEqualNP.Library.SearchHelpers.SatV

def probe (z : Word) : Word := gather (finish z)

def chooser (z : Word) : Word := choose (probe z) (BackdoorPathCore.code z)

def step : Word → Word := advanceUsing probe chooser

def endState : Word × Word → Word := endStateUsing probe chooser

def query (q : Word × Word) : Word := finish (endState q)

theorem query_cpt : ComputableInPolyTime encodePair (fun x : Word => x) query := by
  have hProbe := cpt_comp finish_cpt gather_cpt
  have hBits := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have h := cpt_comp (endStateUsing_cpt hProbe (choose_cpt hProbe hBits)) finish_cpt
  exact h

theorem finish_enc (φ : CNF) (k v : List ℕ) (b : Word) :
    finish (pack (encodeCNF φ) (names k) (names v) b) =
      encodeCNF (restrict (valueOf k v) φ) := by
  simp only [finish, pack, formula, selected, setTrue, unpairB_pairB, run_enc]

def bad (φ : CNF) (k v : List ℕ) : Option Clause :=
  firstWide (restrict (valueOf k v) φ)

theorem probe_enc (φ : CNF) (k v : List ℕ) (b : Word) :
    probe (pack (encodeCNF φ) (names k) (names v) b) =
      ((bad φ k v).map FirstWideClause.names).getD [] := by
  unfold probe
  rw [finish_enc, gather_enc]
  rfl

theorem step_done (φ : CNF) (k v : List ℕ) (b : Word) (h : bad φ k v = none) :
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names k) (names v) b := by
  have hp := probe_enc φ k v b
  rw [h] at hp
  simp [step, advanceUsing, hp, sel]

theorem step_next (φ : CNF) (k v : List ℕ) (b : Word) (c : Clause)
    (h : bad φ k v = some c) (l : Literal) (hl : l ∈ c)
    (hchoose : choose (FirstWideClause.names c) b = vcode l.1) :
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names (k ++ [l.1]))
        (names (v ++ if b.tail.tail.headD false then [l.1] else [])) b.tail.tail.tail := by
  have hc := firstWide_some h
  have hn : FirstWideClause.names c ≠ [] := names_ne_nil c (by intro he; simp [he] at hc)
  obtain ⟨c₀, h₀, hmem, _⟩ := mem_residual hc.1 hl
  have hlen := vcode_bound h₀ hmem
  have hp := probe_enc φ k v b
  simp only [h, Option.map_some, Option.getD_some, pack] at hp
  simp only [step, advanceUsing, chooser, pack, formula, selected, setTrue, BackdoorPathCore.code,
    unpairB_pairB, hp, hchoose, cut_eq, List.take_of_length_le hlen]
  cases hbit : b.tail.tail.head?.getD false <;> simp at hbit <;>
    simp [sel, hn, bflag, hbit, names, List.flatMap_append]

theorem iter_valid (φ : CNF) (k v : List ℕ) (b : Word) (n : ℕ) :
    ∃ k' v' : List ℕ, ∃ b' : Word,
      step^[n] (pack (encodeCNF φ) (names k) (names v) b) =
        pack (encodeCNF φ) (names k') (names v') b' := by
  induction n generalizing k v b with
  | zero => exact ⟨k, v, b, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases h : bad φ k v with
    | none =>
      rw [step_done φ k v b h]
      exact ih k v b
    | some c =>
      have hc := firstWide_some h
      obtain ⟨l, hl, hchoose⟩ := choose_member c b (by intro e; simp [e] at hc)
      rw [step_next φ k v b c h l hl hchoose]
      exact ih _ _ _

theorem query_sound (φ : CNF) (b : Word)
    (h : query (encodeCNF φ, b) ∈ KSAT 2) : Satisfiable φ := by
  obtain ⟨k, v, b', he⟩ := iter_valid φ [] [] b b.length
  have he' : query (encodeCNF φ, b) = encodeCNF (restrict (valueOf k v) φ) := by
    change finish (step^[b.length] (pack (encodeCNF φ) [] [] b)) = _
    change step^[b.length] (pack (encodeCNF φ) [] [] b) = _ at he
    rw [he, finish_enc]
  obtain ⟨ψ, _, hc, hs⟩ := h
  rw [he'] at hc
  have eq := PEqualNP.Library.SearchHelpers.encodeCNF_injective hc
  rw [eq] at hs
  obtain ⟨σ, hσ, _⟩ := (sat_restrict_iff _ _).mp hs
  exact ⟨σ, hσ⟩

end PEqualNP.Outside.WeakWideMachine
