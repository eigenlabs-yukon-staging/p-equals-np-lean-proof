import PEqualNP.Outside.BoundedPartialAssignmentProjection
import PEqualNP.Outside.RenamableHornSATInP

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.RestrictCnfHelpers (restrict sat_restrict_iff)
open PEqualNP.Outside (BoundedPartialAssignmentProjection RenamableHornSATInP)

theorem PEqualNP.Outside.SuppliedRenamableHornBackdoorSATInP (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ (φ : CNF) (a : List ℕ),
        let x := List.replicate (encodeCNF φ).length true ++
          false :: (encodeCNF φ ++ a.flatMap
            (fun i => i.bits.flatMap (fun b => [true, b]) ++ [false, true]))
        2 ^ a.length ≤ p.eval x.length →
        (x ∈ L ↔ ∃ σ : Assignment, CNF.eval σ φ = true ∧
          ∃ flip : Assignment,
            let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
            ∀ c ∈ (φ.filterMap fun d =>
              if d.any (fun l => ρ l.1 == some l.2) then none
              else some (d.filter fun l => (ρ l.1).isNone)),
              (c.filter fun l => xor l.2 (flip l.1)).length ≤ 1) := by
  let H : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧
    ∃ flip : Assignment, ∀ c ∈ φ, (c.filter fun l => xor l.2 (flip l.1)).length ≤ 1}
  obtain ⟨L, hp, hspec⟩ := BoundedPartialAssignmentProjection H RenamableHornSATInP p
  refine ⟨L, hp, ?_⟩
  intro φ a
  dsimp only
  intro h
  rw [hspec φ a h]
  let values (σ : Assignment) : ℕ → Option Bool := fun i => if i ∈ a then some (σ i) else none
  constructor
  · rintro ⟨σ, ψ, he, hsat, flip, hflip⟩
    obtain rfl := PEqualNP.Library.SearchHelpers.encodeCNF_injective he
    obtain ⟨τ, hτ, ha⟩ := (sat_restrict_iff (values σ) φ).mp hsat
    have hρ : values τ = values σ := by
      funext i
      by_cases hi : i ∈ a
      · have hv := ha i (σ i) (by simp [values, hi])
        simp [values, hi, hv]
      · simp [values, hi]
    refine ⟨τ, hτ, flip, ?_⟩
    change ∀ c ∈ restrict (values τ) φ, (c.filter fun l => xor l.2 (flip l.1)).length ≤ 1
    rw [hρ]
    exact hflip
  · rintro ⟨σ, hs, flip, hflip⟩
    refine ⟨σ, restrict (values σ) φ, rfl, ?_, flip, hflip⟩
    apply (sat_restrict_iff (values σ) φ).mpr
    refine ⟨σ, hs, ?_⟩
    intro i b he
    by_cases hi : i ∈ a <;> simp_all [values]
