import PEqualNP.Outside.AdaptiveWidthPathCore
import PEqualNP.Outside.WeakWideMachine
import PEqualNP.Outside.BackdoorSearchFacts
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Outside.WideBackdoorBranch
import PEqualNP.Outside.WideClauseChoice
import PEqualNP.Outside.BinaryNameChoice

namespace PEqualNP.Outside.AdaptiveWidthPathSemantics

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Search
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack formula selected setTrue finish cut_eq)
open PEqualNP.Outside.FirstWideCollector (gather gather_cpt)
open PEqualNP.Outside.FirstWideClause (firstWide firstWide_some names_ne_nil gather_enc)
open PEqualNP.Outside.BinaryNameChoice (choose choose_cpt choose_member)
open PEqualNP.Outside.AdaptiveWidthPathCore
open PEqualNP.Outside.WeakWideMachine (probe probe_enc finish_enc bad)
open PEqualNP.Outside.BackdoorSearchFacts (vcode_bound)
open PEqualNP.Outside.WideBackdoorBranch (mem_residual)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers
open PEqualNP.Library.SearchHelpers.SatV

open PEqualNP.Outside.WidthDigitClock
open PEqualNP.Outside.NameDigitClock (clock_codes)

def digits (c : Clause) : ℕ := (c.length - 1).size

private theorem clock_enc (c : Clause) :
    NameDigitClock.clock (FirstWideClause.names c) = un (digits c) := by
  unfold FirstWideClause.names
  rw [clock_codes, List.length_map]
  rfl

private theorem indices_enc (φ : CNF) (k v : List ℕ) (b : Word) (c : Clause)
    (h : bad φ k v = some c) :
    indices (pack (encodeCNF φ) (names k) (names v) b) = b.take (digits c) := by
  unfold indices
  rw [probe_enc, h]
  simp [clock_enc, pack, BackdoorPathCore.code,
    unpairB_pairB, cut_eq, un_length]

private theorem suffix_enc (φ : CNF) (k v : List ℕ) (b : Word) (c : Clause)
    (h : bad φ k v = some c) :
    suffix (pack (encodeCNF φ) (names k) (names v) b) = b.drop (digits c) := by
  unfold suffix
  rw [probe_enc, h]
  simp [clock_enc, pack, BackdoorPathCore.code,
    unpairB_pairB, skip_eq, un_length]

theorem step_done (φ : CNF) (k v : List ℕ) (b : Word) (h : bad φ k v = none) :
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names k) (names v) b := by
  have hp := probe_enc φ k v b
  rw [h] at hp
  simp [step, hp, sel]

theorem step_next (φ : CNF) (k v : List ℕ) (b : Word) (c : Clause)
    (h : bad φ k v = some c) (l : Literal) (hl : l ∈ c)
    (hchoose : choose (FirstWideClause.names c, (b.take (digits c))) = vcode l.1) :
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names (k ++ [l.1]))
        (names (v ++ if (b.drop (digits c)).headD false then [l.1] else [])) (b.drop (digits c)).tail := by
  have hc := firstWide_some h
  have hn : FirstWideClause.names c ≠ [] := names_ne_nil c (by intro he; simp [he] at hc)
  obtain ⟨c₀, h₀, hmem, _⟩ := mem_residual hc.1 hl
  have hlen := vcode_bound h₀ hmem
  have hp := probe_enc φ k v b
  simp only [h, Option.map_some, Option.getD_some] at hp
  have hi := indices_enc φ k v b c h
  have hs := suffix_enc φ k v b c h
  simp only [step, chooser, hp, hi, hs, hchoose]
  simp only [pack, formula, selected, setTrue, unpairB_pairB, cut_eq, List.take_of_length_le hlen]
  cases hbit : (b.drop (digits c)).head?.getD false <;> (try simp at hbit) <;>
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
      obtain ⟨l, hl, hchoose⟩ := choose_member c (b.take (digits c)) (by intro e; simp [e] at hc)
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

end PEqualNP.Outside.AdaptiveWidthPathSemantics
