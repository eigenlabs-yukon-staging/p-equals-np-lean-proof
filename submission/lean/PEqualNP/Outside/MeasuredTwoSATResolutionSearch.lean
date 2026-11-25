import PEqualNP.Outside.MeasuredBoundedWidthRefutationSearch
import PEqualNP.Outside.TwoSATWidthTwoRefutation

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Search

/-- The width-two search is complete for all unsatisfiable canonical
width-two formulas and returns an exact resolution refutation. -/
theorem MeasuredTwoSATResolutionSearch :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, IsKCNF 2 φ →
        (search (encodeCNF φ) = [] ↔ Satisfiable φ) ∧
        (¬ Satisfiable φ → ∃ ρ : CNF, search (encodeCNF φ) = encodeCNF ρ ∧
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) ∧
          ∀ d ∈ ρ.map List.toFinset, Finset.card d ≤ 2) := by
  classical
  obtain ⟨search,hs,hss⟩ := MeasuredBoundedWidthRefutationSearch 2
  refine ⟨search,hs,fun φ hφ => ?_⟩
  have hcorrect : search (encodeCNF φ) ≠ [] ↔ ¬ Satisfiable φ :=
    (hss φ).1.trans (TwoSATWidthTwoRefutation φ hφ).symm
  constructor
  · constructor
    · intro he
      by_contra hn
      exact (hcorrect.mpr hn) he
    · intro good
      by_contra hne
      exact (hcorrect.mp hne) good
  · exact fun h => (hss φ).2 (hcorrect.mpr h)

end PEqualNP.Outside
