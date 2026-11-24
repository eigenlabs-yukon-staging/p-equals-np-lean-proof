import PEqualNP.Library.Machines.NormalForm

open PEqualNP.Library

theorem PEqualNP.Outside.DecideFromWitnessSearch
    (L : Language Bool) (R : Set (List Bool × List Bool))
    (p : Polynomial ℕ) (s : List Bool → List Bool)
    (hR : DecidableInPolyTime encodePair R)
    (hs : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) s)
    (hL : ∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R)
    (hfind : ∀ x ∈ L, (s x).length ≤ p.eval x.length ∧ (x, s x) ∈ R) :
    L ∈ P := by
  obtain ⟨verify, hver, htime⟩ := hR
  refine ⟨fun x => decide ((s x).length ≤ p.eval x.length) && verify (x, s x), ?_, ?_⟩
  · intro x
    simp only [Bool.and_eq_true, decide_eq_true_eq, ← hver]
    exact ⟨hfind x, fun ⟨hlen, hmem⟩ => (hL x).2 ⟨s x, hlen, hmem⟩⟩
  · exact Machines.cpt_comp (Machines.cpt_pair Machines.cpt_id hs)
      (Machines.nf_decider verify p htime)
