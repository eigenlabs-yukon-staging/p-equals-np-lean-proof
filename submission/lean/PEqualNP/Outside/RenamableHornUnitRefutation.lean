import PEqualNP.Outside.RUPPolarityInvariance
import PEqualNP.Outside.HornUnitRefutation

namespace PEqualNP.Outside

open PEqualNP.Search

private theorem sat_unflip (r : Assignment) (φ : CNF)
    (hs : Satisfiable (φ.map (fun c => c.map (fun l => (l.1,xor l.2 (r l.1)))))) :
    Satisfiable φ := by
  obtain ⟨σ,hσ⟩ := hs
  refine ⟨fun x => xor (σ x) (r x),List.all_eq_true.mpr (fun c hc => ?_)⟩
  have hm := List.mem_map_of_mem (f := fun c : Clause => c.map (fun l => (l.1,xor l.2 (r l.1)))) hc
  obtain ⟨l,hl,hval⟩ := List.any_eq_true.mp (List.all_eq_true.mp hσ _ hm)
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hl
  apply List.any_eq_true.mpr
  refine ⟨m,hm,?_⟩
  simp only [Literal.eval,beq_iff_eq] at hval ⊢
  rw [hval]
  cases m.2 <;> cases r m.1 <;> rfl

/-- Unsatisfiable renamable Horn formulas have the same one-clause
RUP certificate as Horn formulas, with no renaming in the certificate. -/
theorem RenamableHornUnitRefutation (φ : CNF)
    (guard : ∃ r : Assignment, ∀ c ∈ φ,
      ((c.map (fun l => (l.1,xor l.2 (r l.1)))).filter (fun l => l.2)).length ≤ 1) :
    ¬Satisfiable φ ↔
      IsRUP {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} ∅ := by
  change ¬Satisfiable φ ↔ IsRUP (clauseSet φ) ∅
  constructor
  · intro h
    obtain ⟨r,hr⟩ := guard
    let ψ := φ.map (fun c => c.map (fun l => (l.1,xor l.2 (r l.1))))
    have hH (c : Clause) (hc : c ∈ ψ) : (c.filter (fun l => l.2)).length ≤ 1 := by
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact hr d hd
    have hSat : ¬ Satisfiable ψ := fun hs => h (sat_unflip r φ hs)
    have hu : IsRUP (clauseSet ψ) ∅ := (HornUnitRefutation ψ hH).mp hSat
    rw [show clauseSet ψ = _ from clauseSet_flip r φ] at hu
    have hi := RUPPolarityInvariance r (clauseSet φ) ∅
    dsimp only at hi
    rw [Finset.image_empty] at hi
    exact hi.mp hu
  · intro hr
    apply rup_run_refutes φ [[]] _ (by simp)
    apply (rup_run_cons φ [] []).mpr
    exact ⟨by simpa using hr,.nil⟩

end PEqualNP.Outside
