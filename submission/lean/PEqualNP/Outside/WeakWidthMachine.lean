import PEqualNP.Outside.BackdoorChunkCore
import PEqualNP.Outside.WeakWideMachine
import PEqualNP.Outside.BackdoorSearchFacts
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Outside.WideBackdoorBranch
import PEqualNP.Outside.WideClauseChoice
import PEqualNP.Outside.BoundedWidthChoice

namespace PEqualNP.Outside.WeakWidthMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.BackdoorPathCore
open PEqualNP.Outside.FirstWideCollector (gather gather_cpt)
open PEqualNP.Outside.FirstWideClause (firstWide firstWide_some names_ne_nil gather_enc)
open PEqualNP.Outside.BoundedWidthChoice (choose choose_cpt choose_member)
open PEqualNP.Outside.BackdoorChunkCore
open PEqualNP.Outside.WeakWideMachine (probe probe_enc finish_enc bad)
open PEqualNP.Outside.BackdoorSearchFacts (vcode_bound)
open PEqualNP.Outside.WideBackdoorBranch (mem_residual)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers
open PEqualNP.Library.SearchHelpers.SatV

def chooser (digits : ℕ) (z : Word) : Word := choose digits (probe z) (BackdoorPathCore.code z)

def step (digits : ℕ) : Word → Word := advanceChunk digits probe (chooser digits)

def endState (digits : ℕ) : Word × Word → Word := endStateChunk digits probe (chooser digits)

def query (digits : ℕ) (q : Word × Word) : Word := finish (endState digits q)

theorem query_cpt (digits : ℕ) : ComputableInPolyTime encodePair (fun x : Word => x) (query digits) := by
  have hProbe := cpt_comp finish_cpt gather_cpt
  have hBits := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have h := cpt_comp (endStateChunk_cpt digits hProbe (choose_cpt digits hProbe hBits)) finish_cpt
  exact h

theorem step_done (digits : ℕ) (φ : CNF) (k v : List ℕ) (b : Word) (h : bad φ k v = none) :
    step digits (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names k) (names v) b := by
  have hp := probe_enc φ k v b
  rw [h] at hp
  simp [step, advanceChunk, hp, sel]

theorem step_next (digits : ℕ) (φ : CNF) (k v : List ℕ) (b : Word) (c : Clause)
    (h : bad φ k v = some c) (l : Literal) (hl : l ∈ c)
    (hchoose : choose digits (FirstWideClause.names c) b = vcode l.1) :
    step digits (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names (k ++ [l.1]))
        (names (v ++ if (b.drop digits).headD false then [l.1] else [])) (b.drop (digits + 1)) := by
  have hc := firstWide_some h
  have hn : FirstWideClause.names c ≠ [] := names_ne_nil c (by intro he; simp [he] at hc)
  obtain ⟨c₀, h₀, hmem, _⟩ := mem_residual hc.1 hl
  have hlen := vcode_bound h₀ hmem
  have hp := probe_enc φ k v b
  simp only [h, Option.map_some, Option.getD_some, pack] at hp
  simp only [step, advanceChunk, chooser, pack, formula, selected, setTrue, BackdoorPathCore.code,
    unpairB_pairB, hp, hchoose, cut_eq, List.take_of_length_le hlen]
  cases hbit : (b.drop digits).head?.getD false <;> simp at hbit <;>
    simp [sel, hn, bflag, hbit, names, List.flatMap_append]

theorem iter_valid (digits : ℕ) (φ : CNF) (k v : List ℕ) (b : Word) (n : ℕ) :
    ∃ k' v' : List ℕ, ∃ b' : Word,
      (step digits)^[n] (pack (encodeCNF φ) (names k) (names v) b) =
        pack (encodeCNF φ) (names k') (names v') b' := by
  induction n generalizing k v b with
  | zero => exact ⟨k, v, b, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases h : bad φ k v with
    | none =>
      rw [step_done digits φ k v b h]
      exact ih k v b
    | some c =>
      have hc := firstWide_some h
      obtain ⟨l, hl, hchoose⟩ := choose_member digits c b (by intro e; simp [e] at hc)
      rw [step_next digits φ k v b c h l hl hchoose]
      exact ih _ _ _

theorem query_sound (digits : ℕ) (φ : CNF) (b : Word)
    (h : query digits (encodeCNF φ, b) ∈ KSAT 2) : Satisfiable φ := by
  obtain ⟨k, v, b', he⟩ := iter_valid digits φ [] [] b b.length
  have he' : query digits (encodeCNF φ, b) = encodeCNF (restrict (valueOf k v) φ) := by
    change finish ((step digits)^[b.length] (pack (encodeCNF φ) [] [] b)) = _
    change (step digits)^[b.length] (pack (encodeCNF φ) [] [] b) = _ at he
    rw [he, finish_enc]
  obtain ⟨ψ, _, hc, hs⟩ := h
  rw [he'] at hc
  have eq := PEqualNP.Library.SearchHelpers.encodeCNF_injective hc
  rw [eq] at hs
  obtain ⟨σ, hσ, _⟩ := (sat_restrict_iff _ _).mp hs
  exact ⟨σ, hσ⟩

end PEqualNP.Outside.WeakWidthMachine
