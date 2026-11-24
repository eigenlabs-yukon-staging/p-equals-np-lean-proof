import PEqualNP.Outside.RestrictCnfHelpers

open PEqualNP.Search PEqualNP.Outside.RestrictCnfHelpers

theorem PEqualNP.Outside.WeakBackdoorStrictExample :
    let φ : CNF := [[(0, true), (1, true), (2, true), (3, true)]]
    IsKCNF 4 φ ∧
    (∃ (a : Finset ℕ) (σ : Assignment), a.card = 1 ∧ CNF.eval σ φ = true ∧
      (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
       IsKCNF 2 (φ.filterMap fun c =>
         if c.any (fun l => ρ l.1 == some l.2) then none
         else some (c.filter fun l => (ρ l.1).isNone)))) ∧
    (∀ a : Finset ℕ, a.card ≤ 1 →
      ¬ ∀ c ∈ φ, (c.filter fun l => decide (l.1 ∉ a)).length ≤ 2) := by
  dsimp only
  refine ⟨by simp [IsKCNF], ⟨{0}, fun _ => true, by simp, rfl, ?_⟩, ?_⟩
  · simp [IsKCNF, List.filterMap_cons]
  · intro a hcard hs
    have he := hs [(0, true), (1, true), (2, true), (3, true)] (by simp)
    have hsmall := Finset.card_le_one.mp hcard
    by_cases h₀ : 0 ∈ a <;> by_cases h₁ : 1 ∈ a <;>
      by_cases h₂ : 2 ∈ a <;> by_cases h₃ : 3 ∈ a <;>
      simp [h₀, h₁, h₂, h₃] at he <;> grind
