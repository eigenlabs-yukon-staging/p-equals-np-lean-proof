import PEqualNP.Library.L031
import PEqualNP.Outside.PrefixDecideHelpers

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.PrefixDecideHelpers

theorem PEqualNP.Outside.PrefixExtensionReducesToSAT
    (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) :
    ∃ reduce : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) reduce ∧
      ∀ x pre : List Bool,
        (∃ t : List Bool, (pre ++ t).length ≤ p.eval x.length ∧ (x, pre ++ t) ∈ R) ↔
          reduce (x, pre) ∈ PEqualNP.Search.SAT := by
  obtain ⟨red, hred, hspec⟩ := L031.2 (extensions R p) (extensions_np R p hR)
  refine ⟨fun q => red (pairB q.1 q.2), cpt_comp cpt_pairB hred, ?_⟩
  intro x pre
  rw [← hspec]
  change (∃ t, good R p x (pre ++ t)) ↔
    ∃ t, good R p (unpairB (pairB x pre)).1 ((unpairB (pairB x pre)).2 ++ t)
  simp only [unpairB_pairB]
