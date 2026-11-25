import PEqualNP.Library.L010
import PEqualNP.Library.L045
import PEqualNP.Outside.IndexedWitnessProjection

namespace PEqualNP.Outside

open PEqualNP.Library

/-- A uniform, polynomially clocked complete witness generator for each bounded verifier
would suffice for the collapse. The generator's completeness is the explicit hypothesis. -/
theorem IndexedVerifierCollapse
    (cover : ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
      (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) →
      ∃ (clock : List Bool → List Bool) (generate : List Bool × List Bool → List Bool),
        ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) clock ∧
        ComputableInPolyTime encodePair (fun x : List Bool => x) generate ∧
        ∀ x : List Bool, (∃ w : List Bool, (x, w) ∈ R) →
          ∃ i < (clock x).length, (x, generate (List.replicate i true, x)) ∈ R) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro L hL
  obtain ⟨R, p, hR, hbound, hspec⟩ := L045 L hL
  obtain ⟨clock, generate, hc, hg, hcover⟩ := cover R p hR hbound
  have h := IndexedWitnessProjection R hR clock hc generate hg
  have heq : L =
      {x : List Bool | ∃ i < (clock x).length, (x, generate (List.replicate i true, x)) ∈ R} := by
    ext x
    refine (hspec x).trans ⟨hcover x, ?_⟩
    rintro ⟨i, _, hi⟩
    exact ⟨_, hi⟩
  rw [heq]
  exact h

end PEqualNP.Outside
