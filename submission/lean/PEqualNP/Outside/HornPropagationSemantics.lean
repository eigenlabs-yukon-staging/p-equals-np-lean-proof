import PEqualNP.Outside.HornPropagationCore
import PEqualNP.Outside.BackdoorSearchFacts
import PEqualNP.Outside.WideBackdoorBranch

namespace PEqualNP.Outside.HornPropagationSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word cut_eq)
open PEqualNP.Outside.HornPropagationCore
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers
open PEqualNP.Outside.PositiveClauseCollector (pick qualifies result gather gather_enc)
open PEqualNP.Outside.BackdoorSearchFacts (vcode_bound left_decreases)
open PEqualNP.Outside.WideBackdoorBranch (mem_residual)
open PEqualNP.Outside.PartialAssignmentFacts (retained_clause)

def vars (φ : CNF) : Finset ℕ := (φ.flatMap fun c => c.map Prod.fst).toFinset

def simplify (φ : CNF) (k : List ℕ) : CNF := restrict (valueOf k k) φ

def next (φ : CNF) (k : List ℕ) : Option Clause := pick true (simplify φ k)

def state (φ : CNF) (k : List ℕ) : Word := pairB (encodeCNF φ) (names k)

theorem residual_state (φ : CNF) (k : List ℕ) : HornPropagationCore.residual (state φ k) = encodeCNF (simplify φ k) := by
  simp only [HornPropagationCore.residual, state, unpairB_pairB, BackdoorPathCore.finish, BackdoorPathCore.pack,
    BackdoorPathCore.formula, BackdoorPathCore.selected, BackdoorPathCore.setTrue,
    simplify, run_enc]

theorem end_fixed (φ : CNF) (k : List ℕ) (h : next φ k = none) :
    step (state φ k) = state φ k := by
  have hu : gather true (HornPropagationCore.residual (state φ k)) = [] := by
    rw [residual_state, gather_enc]
    change ((next φ k).map (result true)).getD [] = []
    rw [h]
    rfl
  simp [step, unitName, hu, cut_eq, sel]

theorem next_unit {φ : CNF} {k : List ℕ} {c : Clause} (h : next φ k = some c) :
    ∃ i, c = [(i, true)] := by
  have hm := List.find?_some (p := qualifies true) h
  have h : c.all Prod.snd = true ∧ c.length = 1 := by
    simpa [qualifies] using hm
  rcases c with _ | ⟨l, cs⟩
  · simp at h
  · rcases cs with _ | ⟨g, gs⟩
    · rcases l with ⟨i, pol⟩
      cases pol
      · simp at h
      · exact ⟨i, rfl⟩
    · simp at h

theorem unit_fresh {φ : CNF} {k : List ℕ} {i : ℕ} (h : next φ k = some [(i, true)]) :
    i ∈ vars φ ∧ i ∉ k ∧ (vcode i).length ≤ (encodeCNF φ).length := by
  have hm : [(i, true)] ∈ simplify φ k := List.mem_of_find?_eq_some h
  obtain ⟨c, hc, hl, hn⟩ := mem_residual hm (List.mem_singleton_self (i, true))
  have hi : i ∈ vars φ := by
    simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
    exact ⟨c, hc, (i, true), hl, rfl⟩
  have hk : i ∉ k := by
    intro hh
    simp [valueOf, hh] at hn
  exact ⟨hi, hk, vcode_bound hc hl⟩

theorem end_next (φ : CNF) (k : List ℕ) (i : ℕ) (h : next φ k = some [(i, true)]) :
    step (state φ k) = state φ (k ++ [i]) := by
  have hu : gather true (HornPropagationCore.residual (state φ k)) = vcode i := by
    rw [residual_state, gather_enc]
    change ((next φ k).map (result true)).getD [] = _
    simp [h, result, FirstWideClause.names]
  have hlen := (unit_fresh h).2.2
  have hunit : unitName (state φ k) = vcode i := by
    unfold unitName
    rw [hu]
    simp [state, unpairB_pairB, cut_eq, List.take_of_length_le hlen]
  unfold step
  dsimp only
  rw [hunit]
  simp [state, unpairB_pairB, vcode_ne_nil, sel, names, List.flatMap_append]

theorem vars_le (φ : CNF) : (vars φ).card ≤ (encodeCNF φ).length := by
  unfold vars
  calc
    _ ≤ (φ.flatMap fun c => c.map Prod.fst).length := List.toFinset_card_le _
    _ ≤ nIt φ := by
      induction φ with
      | nil => simp [nIt]
      | cons c φ ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, nIt] at *
        omega
    _ ≤ _ := nIt_le φ

theorem residual_sat {φ : CNF} {k : List ℕ} {σ : Assignment} (hs : CNF.eval σ φ = true)
    (hk : ∀ i ∈ k, σ i = true) : CNF.eval σ (simplify φ k) = true := by
  have hres := eval_restrict (valueOf k k) σ φ
  have he : merged (valueOf k k) σ = σ := by
    funext i
    by_cases h : i ∈ k
    · simp [merged, valueOf, h, hk i h]
    · simp [merged, valueOf, h]
  simp [simplify, hres, he, hs]

theorem saturate (φ : CNF) (fuel : ℕ) (k : List ℕ)
    (hf : (vars φ \ k.toFinset).card ≤ fuel) :
    ∃ n ≤ fuel, ∃ out : List ℕ,
      next φ out = none ∧ step^[n] (state φ k) = state φ out ∧
      ∀ σ : Assignment, CNF.eval σ φ = true → (∀ i ∈ k, σ i = true) → ∀ i ∈ out, σ i = true := by
  induction fuel using Nat.strong_induction_on generalizing k with
  | ind fuel ih =>
    cases h : next φ k with
    | none => exact ⟨0, Nat.zero_le _, k, h, rfl, fun _ _ hk => hk⟩
    | some c =>
      obtain ⟨i, rfl⟩ := next_unit h
      let k' := k ++ [i]
      have hl := unit_fresh h
      have hlt : (vars φ \ k'.toFinset).card < fuel :=
        (left_decreases (vars φ) k i hl.1 hl.2.1).trans_le hf
      obtain ⟨n, hn, out, hout, hstep, hagree⟩ := ih _ hlt k' le_rfl
      refine ⟨n + 1, by omega, out, hout, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, end_next φ k i h]
        exact hstep
      · intro σ hs hk
        apply hagree σ hs
        have hres := residual_sat hs hk
        have hm : [(i, true)] ∈ simplify φ k := List.mem_of_find?_eq_some h
        have hcl := List.all_eq_true.mp hres _ hm
        have hv : σ i = true := by
          simpa [Clause.eval, Literal.eval] using hcl
        intro j hj
        rcases List.mem_append.mp hj with hin | hin
        · exact hk j hin
        · obtain rfl := List.mem_singleton.mp hin
          exact hv

theorem saturated_state (φ : CNF) :
    ∃ k : List ℕ, next φ k = none ∧ endState (encodeCNF φ) = state φ k ∧
      ∀ σ : Assignment, CNF.eval σ φ = true → ∀ i ∈ k, σ i = true := by
  obtain ⟨n, hn, k, hk, he, ha⟩ := saturate φ (encodeCNF φ).length [] (by simpa using vars_le φ)
  refine ⟨k, hk, ?_, fun σ h => ha σ h (by simp)⟩
  unfold endState
  change step^[(encodeCNF φ).length] (state φ []) = state φ k
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, he, Function.iterate_fixed (end_fixed φ k hk)]

end PEqualNP.Outside.HornPropagationSemantics
