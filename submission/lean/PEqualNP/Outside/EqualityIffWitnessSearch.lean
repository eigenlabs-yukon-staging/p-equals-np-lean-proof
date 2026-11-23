import PEqualNP.Outside.PrefixSelector
import PEqualNP.Outside.CollapseFromWitnessSearch
import PEqualNP.Outside.P_subset_NP

open PEqualNP.Library

theorem PEqualNP.Outside.EqualityIffWitnessSearch :
    P = NP ↔
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
        ∃ s : List Bool → List Bool,
          ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) s ∧
          ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
            (s x).length ≤ p.eval x.length ∧ (x, s x) ∈ R := by
  constructor
  · intro equality R p hR
    have hp := PrefixDecideHelpers.extensions_np R p hR
    rw [← equality] at hp
    exact PrefixSelector.selector_of_extensions R p hR hp
  · exact fun hs => Set.Subset.antisymm P_subset_NP (CollapseFromWitnessSearch hs)
