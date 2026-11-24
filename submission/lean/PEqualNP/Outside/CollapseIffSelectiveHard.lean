import PEqualNP.Outside.SelectiveHardImpliesCollapse
import PEqualNP.Outside.CollapseIffSparseHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

/-- The pinned equality is equivalent to the existence of a P-selective NP-hard target. -/
theorem CollapseIffSelectiveHard :
    P = NP ↔ ∃ (B : Language Bool) (choose : List Bool × List Bool → List Bool), NPHard B ∧
      ComputableInPolyTime encodePair (fun x => x) choose ∧
      ∀ x y : List Bool, (choose (x,y) = x ∨ choose (x,y) = y) ∧
        (x ∈ B ∨ y ∈ B → choose (x,y) ∈ B) := by
  constructor
  · intro h
    let pick := fun q : List Bool × List Bool => sel q.1 q.1 q.2
    have hp : ComputableInPolyTime encodePair (fun x => x) pick := by
      have hf := cpt_comp cpt_pairB (cpt_sel cpt_unpairB1 cpt_unpairB1 cpt_unpairB2)
      apply bf_cptl hf
      rintro ⟨x,y⟩
      simp [pick, unpairB_pairB]
    refine ⟨{[]}, pick, singleton_hard_of_collapse h, hp, fun x y => ?_⟩
    change (pick (x,y) = x ∨ pick (x,y) = y) ∧
      (x = [] ∨ y = [] → pick (x,y) = [])
    by_cases hx : x = [] <;> simp [pick, sel, hx]
  · rintro ⟨B, choose, hB, hc, hs⟩
    exact SelectiveHardImpliesCollapse B hB choose hc hs

end PEqualNP.Outside
