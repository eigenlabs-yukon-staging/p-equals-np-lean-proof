import PEqualNP.Outside.DisjunctiveHardImage

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

/-- A coNP-hard target represents the joint rejection of two NP queries through one
polynomial-time image, with both original inputs in the tagged pair encoding. -/
theorem ConjunctiveCoHardImage (A B : Language Bool) (hA : A ∈ NP)
    (hB : ∀ L ∈ coNP, PolyTimeReducible L B) :
    ∃ f : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x => x) f ∧
      ∀ x y : List Bool, f (x,y) ∈ B ↔ x ∉ A ∧ y ∉ A := by
  have hc : (disjunctiveQueryLanguage A)ᶜ ∈ coNP := by
    change ((disjunctiveQueryLanguage A)ᶜ)ᶜ ∈ NP
    rw [compl_compl]
    exact disjunctiveQueryLanguage_np A hA
  obtain ⟨f, hf, hs⟩ := hB _ hc
  refine ⟨fun p => f (pairB p.1 p.2), cpt_comp cpt_pairB hf, fun x y => ?_⟩
  refine (hs (pairB x y)).symm.trans ?_
  change (¬ ((unpairB (pairB x y)).1 ∈ A ∨ (unpairB (pairB x y)).2 ∈ A)) ↔ _
  simp [unpairB_pairB]

end PEqualNP.Outside
