import PEqualNP.Outside.SatIffWitnessSearch
import PEqualNP.Outside.LogWitnessCodesInP

open PEqualNP.Library PEqualNP.Library.Machines

theorem PEqualNP.Outside.SatIffLogWitnessCodes :
    PEqualNP.Search.SAT ∈ P ↔
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
        ∃ (decode : List Bool × List Bool → List Bool) (c d : ℕ),
          ComputableInPolyTime encodePair (fun w : List Bool => w) decode ∧
          ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
            ∃ code : List Bool, (decode (x, code)).length ≤ p.eval x.length ∧
              (x, decode (x, code)) ∈ R ∧ code.length ≤ c * Nat.log2 (x.length + 1) + d := by
  constructor
  · intro hsat R p hR
    obtain ⟨s, hs, hfind⟩ := SatIffWitnessSearch.mp hsat R p hR
    refine ⟨fun q => s q.1, 0, 0, cpt_comp cpt_fst hs, ?_⟩
    intro x hx
    obtain ⟨hlen, hmem⟩ := hfind x hx
    exact ⟨[], hlen, hmem, by simp⟩
  · intro hall
    obtain ⟨R, p, hR, hL⟩ := L031.1
    obtain ⟨decode, c, d, hdecode, hshort⟩ := hall R p hR
    exact LogWitnessCodesInP PEqualNP.Search.SAT R p c d decode hdecode hR hL
      fun x hx => hshort x ((hL x).mp hx)
