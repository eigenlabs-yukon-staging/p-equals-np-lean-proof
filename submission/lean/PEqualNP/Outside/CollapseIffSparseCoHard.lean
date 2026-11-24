import PEqualNP.Outside.CollapseIffSparseHard
import PEqualNP.Outside.SparseCoHardImpliesCollapse
import PEqualNP.Library.L008

namespace PEqualNP.Outside

open PEqualNP.Library

/-- The reference collapse is equivalent to the existence of a sparse coNP-hard target. -/
theorem CollapseIffSparseCoHard :
    P = NP ↔ ∃ (B : Language Bool) (q : Polynomial Nat),
      (∀ L ∈ coNP, PolyTimeReducible L B) ∧
      ∀ (n : Nat) (ys : Finset (List Bool)),
        (∀ y ∈ ys, y ∈ B ∧ y.length = n) → ys.card ≤ q.eval n := by
  constructor
  · intro h
    refine ⟨({[]} : Language Bool), 1, ?_, fun n ys hy => ?_⟩
    · intro A hA
      have hc : Aᶜ ∈ NP := hA
      have hcp : Aᶜ ∈ P := h.symm ▸ hc
      have hAp : A ∈ P := by simpa using L008 (Aᶜ) hcp
      exact singleton_hard_of_collapse h A (L010 hAp)
    · have hsub : ys ⊆ ({[]} : Finset (List Bool)) := by
        intro y hmem
        exact Finset.mem_singleton.mpr (show y = [] from (hy y hmem).1)
      simpa using Finset.card_le_card hsub
  · rintro ⟨B, q, hB, hs⟩
    exact SparseCoHardImpliesCollapse B hB ((Polynomial.X + 1) * q)
      (sparseCumulativeOfPointwise B q hs)

end PEqualNP.Outside
