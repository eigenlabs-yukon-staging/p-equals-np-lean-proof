import PEqualNP.Outside.LogWitnessesInP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

theorem PEqualNP.Outside.LogWitnessCodesInP
    (L : Language Bool) (R : Set (List Bool × List Bool)) (p : Polynomial ℕ) (c d : ℕ)
    (decode : List Bool × List Bool → List Bool)
    (hdecode : ComputableInPolyTime encodePair (fun w : List Bool => w) decode)
    (hR : DecidableInPolyTime encodePair R)
    (hL : ∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R)
    (hshort : ∀ x ∈ L, ∃ code : List Bool,
      (decode (x, code)).length ≤ p.eval x.length ∧ (x, decode (x, code)) ∈ R ∧
      code.length ≤ c * Nat.log2 (x.length + 1) + d) :
    L ∈ P := by
  let R' : Set (List Bool × List Bool) :=
    {q | (decode q).length ≤ p.eval q.1.length ∧ (q.1, decode q) ∈ R}
  let p' : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) + Polynomial.C d
  have hbound (x code : List Bool) (hc : code.length ≤ c * Nat.log2 (x.length + 1) + d) :
      code.length ≤ p'.eval x.length := by
    simp only [p', Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    exact hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.log2_le_self _)) _)
  have hR' : DecidableInPolyTime encodePair R' := by
    obtain ⟨verify, hv, hc⟩ := hR
    refine ⟨fun q => decide ((decode q).length ≤ p.eval q.1.length) &&
        verify (q.1, decode q), ?_, ?_⟩
    · intro q
      simp only [R', Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq, hv]
    · exact cpt_comp (cpt_pairG cpt_fst hdecode) (nf_decider verify p hc)
  have short (x : List Bool) (hx : x ∈ L) :
      ∃ code : List Bool, code.length ≤ p'.eval x.length ∧
        (x, code) ∈ R' ∧ code.length ≤ c * Nat.log2 (x.length + 1) + d := by
    obtain ⟨code, hl, hm, hs⟩ := hshort x hx
    exact ⟨code, hbound x code hs, ⟨hl, hm⟩, hs⟩
  apply LogWitnessesInP L R' p' c d hR' ?_ short
  intro x
  exact ⟨fun hx => let ⟨code, hlen, hmem, _⟩ := short x hx
                  ⟨code, hlen, hmem⟩,
    fun ⟨code, _, hlen, hmem⟩ => (hL x).mpr ⟨decode (x, code), hlen, hmem⟩⟩
