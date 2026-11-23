import PEqualNP.Library.L031
import PEqualNP.Library.L018
import PEqualNP.Outside.EqualityIffWitnessSearch

open PEqualNP.Library

theorem PEqualNP.Outside.SatIffWitnessSearch :
    PEqualNP.Search.SAT ∈ P ↔
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
        ∃ s : List Bool → List Bool,
          ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) s ∧
          ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
            (s x).length ≤ p.eval x.length ∧ (x, s x) ∈ R :=
  (L018 PEqualNP.Search.SAT L031).trans EqualityIffWitnessSearch
