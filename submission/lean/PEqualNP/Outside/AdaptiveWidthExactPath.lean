import PEqualNP.Outside.AdaptiveWidthPathComplete

namespace PEqualNP.Outside.AdaptiveWidthExactPath

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack finish)
open PEqualNP.Outside.AdaptiveWidthPathCore (step endState query)
open PEqualNP.Outside.AdaptiveWidthPathSemantics (digits step_done)
open PEqualNP.Outside.AdaptiveWidthPathComplete (record record_length step_follow)
open PEqualNP.Outside.WeakWideMachine (bad finish_enc)
open PEqualNP.Outside.FirstWideClause (firstWide_none)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.RestrictCnfHelpers (restrict sat_restrict_iff)

abbrev Visit := Clause × Literal

def visitedNames (path : List Visit) : List ℕ := path.map (fun v => v.2.1)

def cost (path : List Visit) : ℕ := (path.map (fun v => digits v.1 + 1)).sum

def valid (φ : CNF) (σ : Assignment) (k : List ℕ) (path : List Visit) : Prop :=
  ∀ i v, path[i]? = some v →
    let chosen := k ++ visitedNames (path.take i)
    bad φ chosen (chosen.filter σ) = some v.1 ∧ v.2 ∈ v.1

theorem follow (φ : CNF) (σ : Assignment) (k : List ℕ) (path : List Visit)
    (h : valid φ σ k path) :
    let k' := k ++ visitedNames path
    ∃ b : Word, b.length = cost path ∧ path.length ≤ b.length ∧
      step^[path.length] (pack (encodeCNF φ) (names k) (names (k.filter σ)) b) =
        pack (encodeCNF φ) (names k') (names (k'.filter σ)) [] := by
  induction path generalizing k with
  | nil =>
    exact ⟨[], rfl, le_rfl, by simp [visitedNames]⟩
  | cons v vs ih =>
    let j := v.2.1
    have head := h 0 v rfl
    simp only [List.take_zero, visitedNames, List.map_nil, List.append_nil] at head
    obtain ⟨i, hindex, he⟩ := List.getElem_of_mem head.2
    have hi : i < 2 ^ digits v.1 := by
      have hw := Nat.lt_size_self (v.1.length - 1)
      unfold digits
      omega
    have hsome : v.1[i]? = some v.2 := by
      simp [List.getElem?_eq_getElem hindex, he]
    have tail_valid : valid φ σ (k ++ [j]) vs := by
      intro n w hn
      have hw := h (n + 1) w (by simpa using hn)
      simpa [visitedNames, j, List.append_assoc] using hw
    obtain ⟨b, hb, hl, hstep⟩ := ih (k ++ [j]) tail_valid
    refine ⟨record (digits v.1) i (σ j) b, ?_, ?_, ?_⟩
    · simp [record_length, hb, cost]
    · rw [record_length]
      simp only [List.length_cons]
      omega
    · rw [List.length_cons, Function.iterate_succ_apply,
        step_follow φ k σ v.1 head.1 i v.2 hi hsome b]
      simpa [visitedNames, j, List.append_assoc] using hstep

theorem complete (φ : CNF) (σ : Assignment) (path : List Visit)
    (hσ : CNF.eval σ φ = true) (h : valid φ σ [] path)
    (hdone : bad φ (visitedNames path) ((visitedNames path).filter σ) = none) :
    ∃ b : Word, b.length = cost path ∧ query (encodeCNF φ, b) ∈ KSAT 2 := by
  obtain ⟨b, hb, hl, he⟩ := follow φ σ [] path h
  simp only [List.nil_append, visitedNames, List.map_nil, names, List.flatMap_nil, List.filter_nil] at he
  let k := visitedNames path
  have he' : endState (encodeCNF φ, b) =
      pack (encodeCNF φ) (names k) (names (k.filter σ)) [] := by
    change step^[b.length] (pack (encodeCNF φ) [] [] b) = _
    rw [← Nat.sub_add_cancel hl, Function.iterate_add_apply, he]
    exact Function.iterate_fixed (step_done φ k (k.filter σ) [] hdone) _
  refine ⟨b, hb, ?_⟩
  unfold query
  rw [he', finish_enc]
  refine ⟨restrict (valueOf k (k.filter σ)) φ, (firstWide_none _).mp hdone, rfl, ?_⟩
  apply (sat_restrict_iff _ _).mpr
  refine ⟨σ, hσ, ?_⟩
  intro i v hv
  by_cases hm : i ∈ k
  · cases hv' : σ i <;> simpa [valueOf, hm, List.mem_filter, hv'] using hv
  · simp [valueOf, hm] at hv

end PEqualNP.Outside.AdaptiveWidthExactPath
