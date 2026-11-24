import PEqualNP.Outside.PartialAssignmentFacts
import PEqualNP.Outside.FirstWideClause

namespace PEqualNP.Outside.WideBackdoorBranch

open PEqualNP.Search
open PEqualNP.Outside.PartialAssignmentFacts (assignment valueOf_filter retained_clause)
open PEqualNP.Outside.RestrictCnfHelpers

theorem mem_residual {φ : CNF} {ρ : ℕ → Option Bool} {c : Clause}
    (hc : c ∈ restrict ρ φ) {l : Literal} (hl : l ∈ c) :
    ∃ c₀ ∈ φ, l ∈ c₀ ∧ ρ l.1 = none := by
  obtain ⟨c₀, hc₀, he⟩ := retained_clause hc
  rw [he] at hl
  obtain ⟨h₁, h₂⟩ := List.mem_filter.mp hl
  exact ⟨c₀, hc₀, h₁, Option.isNone_iff_eq_none.mp h₂⟩

theorem residual_width {φ : CNF} {ρ : ℕ → Option Bool} {n : ℕ}
    (hw : IsKCNF n φ) : IsKCNF n (restrict ρ φ) := by
  intro c hc
  obtain ⟨c₀, h₀, h⟩ := retained_clause hc
  rw [h]
  exact (List.length_filter_le _ _).trans (hw c₀ h₀)

theorem wide_hits {φ : CNF} {k a : Finset ℕ} {σ : Assignment} {c : Clause}
    (h : c ∈ restrict (assignment k σ) φ) (hwide : 2 < c.length)
    (hsub : k ⊆ a) (hwidth : IsKCNF 2 (restrict (assignment a σ) φ)) :
    ∃ l ∈ c, l.1 ∈ a := by
  by_contra! miss
  obtain ⟨c₀, hc₀, hstep⟩ := List.mem_filterMap.mp h
  have hf : c₀.any (fun l => assignment k σ l.1 == some l.2) = false := by
    cases hf' : c₀.any (fun l => assignment k σ l.1 == some l.2)
    · rfl
    · simp [hf'] at hstep
  have hres : c₀.filter (fun l => (assignment k σ l.1).isNone) = c := by
    simpa [hf] using hstep
  have he (l : Literal) (hl : l ∈ c₀) : assignment k σ l.1 = assignment a σ l.1 := by
    by_cases hk : l.1 ∈ k
    · simp [assignment, hk, hsub hk]
    · have hm : l ∈ c := by
        rw [← hres]
        exact List.mem_filter.mpr ⟨hl, by simp [assignment, hk]⟩
      simp [assignment, hk, miss l hm]
  have hfa : c₀.any (fun l => assignment a σ l.1 == some l.2) = false := by
    apply Bool.eq_false_iff.mpr
    intro ha
    obtain ⟨l, hl, hv⟩ := List.any_eq_true.mp ha
    have hk : c₀.any (fun l => assignment k σ l.1 == some l.2) = true := by
      apply List.any_eq_true.mpr
      exact ⟨l, hl, by rwa [he l hl]⟩
    rw [hf] at hk
    cases hk
  have hfilter : c₀.filter (fun l => (assignment a σ l.1).isNone) = c := by
    rw [← hres]
    apply List.filter_congr
    intro l hl
    rw [he l hl]
  have hm : c ∈ restrict (assignment a σ) φ :=
    List.mem_filterMap.mpr ⟨c₀, hc₀, by simp [hfa, hfilter]⟩
  have := hwidth c hm
  omega

end PEqualNP.Outside.WideBackdoorBranch
