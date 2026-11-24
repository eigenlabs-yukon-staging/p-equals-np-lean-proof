import PEqualNP.Outside.PolynomialBudgetPartialAssignmentProjection
import PEqualNP.Outside.RenamableHornSATInP

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.RestrictCnfHelpers (restrict sat_restrict_iff)
open PEqualNP.Outside (PolynomialBudgetPartialAssignmentProjection RenamableHornSATInP)

theorem PEqualNP.Outside.PolynomialBudgetWeakRenamableHornBackdoorSATInP (p : Polynomial ℕ) :
    ({x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ (a : List ℕ) (σ flip : Assignment),
        (let n := (φ.flatMap fun c => c.map Prod.fst).toFinset.card
         2 ^ (((n - 1).size + 1) * a.length) ≤ p.eval x.length) ∧ (∀ i ∈ a, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i) ∧ CNF.eval σ φ = true ∧
        let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
        ∀ c ∈ (φ.filterMap fun d =>
          if d.any (fun l => ρ l.1 == some l.2) then none
          else some (d.filter fun l => (ρ l.1).isNone)),
          (c.filter fun l => xor l.2 (flip l.1)).length ≤ 1} : Language Bool) ∈ P := by
  let H : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧
    ∃ flip : Assignment, ∀ c ∈ φ, (c.filter fun l => xor l.2 (flip l.1)).length ≤ 1}
  obtain ⟨L, ⟨dec, hd, ht⟩, hL⟩ := PolynomialBudgetPartialAssignmentProjection H RenamableHornSATInP p
  refine ⟨dec, ?_, ht⟩
  intro x
  refine Iff.trans ?_ (hd x)
  constructor
  · rintro ⟨φ, rfl, a, σ, flip, hk, hm, hs, he⟩
    let ρ : ℕ → Option Bool := fun i => if i ∈ a then some (σ i) else none
    have hsat : Satisfiable (restrict ρ φ) := by
      apply (sat_restrict_iff ρ φ).mpr
      refine ⟨σ, hs, ?_⟩
      intro i b he
      by_cases hm : i ∈ a <;> simp_all [ρ]
    exact (hL _).mpr ⟨φ, rfl, a, σ, hk, hm, restrict ρ φ, rfl, hsat, flip, he⟩
  · intro h
    obtain ⟨φ, rfl, a, σ, hk, hm, ψ, he, hsat, flip, hf⟩ := (hL _).mp h
    obtain rfl := PEqualNP.Library.SearchHelpers.encodeCNF_injective he
    let ρ (τ : Assignment) : ℕ → Option Bool := fun i => if i ∈ a then some (τ i) else none
    obtain ⟨τ, hτ, ha⟩ := (sat_restrict_iff (ρ σ) φ).mp hsat
    have hsame : ρ τ = ρ σ := by
      funext i
      by_cases hi : i ∈ a
      · have hv := ha i (σ i) (by simp [ρ, hi])
        simp [ρ, hi, hv]
      · simp [ρ, hi]
    refine ⟨φ, rfl, a, τ, flip, hk, hm, hτ, ?_⟩
    change ∀ c ∈ restrict (ρ τ) φ, (c.filter fun l => xor l.2 (flip l.1)).length ≤ 1
    rw [hsame]
    exact hf
