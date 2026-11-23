import PEqualNP.Outside.DecideFromWitnessSearch

open PEqualNP.Library

theorem PEqualNP.Outside.CollapseFromWitnessSearch
    (search : ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
        ∃ s : List Bool → List Bool,
          ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) s ∧
          ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
            (s x).length ≤ p.eval x.length ∧ (x, s x) ∈ R) :
    NP ⊆ P := by
  intro L hL
  obtain ⟨R, p, hR, hL⟩ := hL
  obtain ⟨s, hs, hfind⟩ := search R p hR
  exact DecideFromWitnessSearch L R p s hR hs hL fun x hx => hfind x ((hL x).1 hx)
