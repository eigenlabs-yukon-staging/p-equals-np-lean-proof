import PEqualNP.Outside.MeasuredCNFIntersection
import PEqualNP.Outside.UnitPropagationCorrect
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

/-- Decide whether every finite-set clause in the first canonical formula
occurs in the second, regardless of literal order and repetitions. -/
theorem MeasuredCNFSubset :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ U : CNF), test (encodeCNF φ,encodeCNF U) = true ↔
        {c : PEqualNP.ProofComplexity.Clause ℕ | ∃ d ∈ φ, d.toFinset = c} ⊆
        {c : PEqualNP.ProofComplexity.Clause ℕ | ∃ d ∈ U, d.toFinset = c} := by
  obtain ⟨intersect,hi,his⟩ := MeasuredCNFIntersection
  let test := fun p : Raw × Raw => decide (intersect (p.2,p.1) = p.1)
  have hraw := cpt_eqF (cpt_comp (cpt_pair cpt_unpairB2 cpt_unpairB1) hi) cpt_unpairB1
  have ht := cpt_comp (cpt_comp cpt_pairB hraw) bf_cpt_neL
  have htest :
      (fun p : Raw × Raw => !(bflag (decide (intersect (p.2,p.1) = p.1))).isEmpty) = test := by
    funext p
    unfold test
    cases decide (intersect (p.2,p.1) = p.1) <;> rfl
  simp only [unpairB_pairB] at ht
  rw [htest] at ht
  refine ⟨test,ht,fun φ U => ?_⟩
  simp only [test,decide_eq_true_eq,his,encodeCNF_injective.eq_iff]
  rw [List.filter_eq_self]
  constructor
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := hc
    exact of_decide_eq_true (h d hd)
  · intro h d hd
    exact decide_eq_true (h (show d.toFinset ∈ clauseSet φ from ⟨d,hd,rfl⟩))

end PEqualNP.Outside
