import PEqualNP.Outside.OptimalWitnessCheckingCoNPComplete

open PEqualNP.Library

theorem PEqualNP.Outside.OptimalWitnessCheckingIffCollapse :
    P = NP ↔
    ∀ (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R → DecidableInPolyTime encodePair C →
      ∃ L : Language Bool, L ∈ P ∧ ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (x, List.replicate v.length true ++ false :: (v ++ w)) ∉ C :=
  PEqualNP.Outside.OptimalWitnessCheckingIffCollapseProof
