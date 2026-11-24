import PEqualNP.Outside.AtLeastTwoWitnessesInNP

open PEqualNP.Library
open PEqualNP.Outside.PrefixDecideHelpers (Word good)

theorem PEqualNP.Outside.UniqueWitnessAsNPDifference :
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), DecidableInPolyTime encodePair R →
      ∃ A B : Language Bool, A ∈ NP ∧ B ∈ NP ∧
        ∀ x, (x ∈ A ∧ x ∉ B) ↔
          ∃! w : List Bool, w.length ≤ p.eval x.length ∧ (x,w) ∈ R := by
  intro R p hR
  let A : Language Bool := {x | ∃ w : Word, good R p x w}
  let B := TwoWitnesses.language R p
  have ha : A ∈ NP := ⟨R,p,hR,fun _ => Iff.rfl⟩
  refine ⟨A,B,ha,TwoWitnesses.np R p hR,?_⟩
  intro x
  constructor
  · rintro ⟨⟨w,hw⟩,hn⟩
    refine ⟨w,hw,?_⟩
    intro v hv
    by_contra he
    exact hn ⟨v,w,hv,hw,he⟩
  · rintro ⟨w,hw,hu⟩
    refine ⟨⟨w,hw⟩,?_⟩
    rintro ⟨v,z,hv,hz,hne⟩
    exact hne ((hu v hv).trans (hu z hz).symm)
