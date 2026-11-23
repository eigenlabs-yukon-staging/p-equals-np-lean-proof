import PEqualNP.Outside.VariableBudgetSATInP
import PEqualNP.Library.L018
import PEqualNP.Library.L031

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search

theorem PEqualNP.Outside.CollapseIffBudgetedSATReduction :
    P = NP ↔ ∃ p : Polynomial ℕ, PolyTimeReducible SAT
      ({x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧
        2 ^ (φ.flatten.map Prod.fst).toFinset.card ≤ p.eval x.length} : Language Bool) := by
  let B (p : Polynomial ℕ) : Language Bool :=
    {x | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧
      2 ^ (φ.flatten.map Prod.fst).toFinset.card ≤ p.eval x.length}
  change P = NP ↔ ∃ p, PolyTimeReducible SAT (B p)
  rw [← L018 SAT L031]
  constructor
  · rintro ⟨dec, hdec, htime⟩
    have hy : ([] : List Bool) ∈ B 1 := by
      refine ⟨[], rfl, ⟨fun _ => false, rfl⟩, ?_⟩
      simp
    have hn : ([false, false] : List Bool) ∉ B 1 := by
      rintro ⟨φ, hφ, ⟨σ, hσ⟩, _⟩
      have heq : encodeCNF φ = encodeCNF [[]] := hφ
      have hformula := PEqualNP.Library.SearchHelpers.encodeCNF_injective heq
      subst φ
      cases hσ
    refine ⟨1, fun x => sel (if dec x then [true] else []) [false, false] [],
      cpt_sel (cpt_bitFlag htime) (cpt_const _) (cpt_const _), ?_⟩
    intro x
    refine (hdec x).trans ?_
    cases h : dec x <;> simp [sel, h, hy, hn]
  · rintro ⟨p, hred⟩
    exact L016 SAT (B p) hred (VariableBudgetSATInP p)
