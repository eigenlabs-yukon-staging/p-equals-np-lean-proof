import PEqualNP.Library.L010
import PEqualNP.Library.L045
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Outside.PrefixExtensionNP
import PEqualNP.Outside.VerifierSearchFromPrefixDecider

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines

/-- Equality of the pinned classes is equivalent to measured witness search for every
polynomial-time verifier whose accepted words obey a polynomial length bound. -/
theorem VerifierSearchCollapse :
    P = NP ↔
      ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
        DecidableInPolyTime encodePair R →
        (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) →
        ∃ search : List Bool → List Bool,
          ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
          ∀ x : List Bool, (∃ w : List Bool, (x, w) ∈ R) → (x, search x) ∈ R := by
  constructor
  · intro collapse R p hR hb
    obtain ⟨D, hD, hspec⟩ := PrefixExtensionNP R p hR hb
    rw [← collapse] at hD
    exact VerifierSearchFromPrefixDecider R p hR hb D hD hspec
  · intro find
    refine Set.Subset.antisymm L010 ?_
    intro L hL
    obtain ⟨R, p, hR, hb, hspec⟩ := L045 L hL
    obtain ⟨search, hc, hsearch⟩ := find R p hR hb
    obtain ⟨f, hf, hcf⟩ := hR
    refine ⟨fun x => f (x, search x), fun x => ?_, cpt_comp (cpt_pair cpt_id hc) hcf⟩
    exact ⟨fun hx => (hf _).mp (hsearch x ((hspec x).mp hx)),
      fun hx => (hspec x).mpr ⟨_, (hf _).mpr hx⟩⟩

end PEqualNP.Outside
