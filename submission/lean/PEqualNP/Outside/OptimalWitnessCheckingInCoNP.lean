import PEqualNP.Outside.OptimalWitnessCheckingCoNPComplete

open PEqualNP.Library

theorem PEqualNP.Outside.OptimalWitnessCheckingInCoNP
    (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (hC : DecidableInPolyTime encodePair C) :
    ∃ L : Language Bool, L ∈ coNP ∧
      ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (x, List.replicate v.length true ++ false :: (v ++ w)) ∉ C :=
  PEqualNP.Outside.OptimalWitnessCheckingInCoNPProof R C p hR hC

