import PEqualNP.Outside.PolynomialWitnessRecovery

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Universal

/-- Each pinned NP language admits witness production in polynomial time in the
combined input and supplied padding length. The padding required for completeness
can be exponential in the original input length. -/
theorem UnaryPaddedSearchForNP (L : Language Bool) (hL : L ∈ NP) :
    ∃ (R : Set (List Bool × List Bool)) (p : Polynomial Nat)
      (f : List Bool × List Bool → List Bool),
      DecidableInPolyTime encodePair R ∧
      (∀ x w : List Bool, (x,w) ∈ R → w.length ≤ p.eval x.length) ∧
      (∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x,w) ∈ R) ∧
      ComputableInPolyTime encodePair (fun x => x) f ∧
      ∀ x b : List Bool, 2 ^ (p.eval x.length + 1) ≤ b.length + 1 →
        (f (x,b) = [] ∧ x ∉ L) ∨
          ∃ w : List Bool, f (x,b) = true :: w ∧ (x,w) ∈ R := by
  obtain ⟨R, p, ⟨v, hs, hv⟩, hb, hspec⟩ := L045 L hL
  refine ⟨R, p, unaryRecovery v, ⟨v, hs, hv⟩, hb, hspec,
    unaryRecovery_polyTime hv, fun x b hclock => ?_⟩
  rcases unaryRecovery_spec v x b with ⟨hout, hnone⟩ | ⟨j, _, hout, hyes, _⟩
  · left
    refine ⟨hout, fun hmem => ?_⟩
    obtain ⟨w, hw⟩ := (hspec x).mp hmem
    have hidx := idx_lt_of_length_le (hb x w hw)
    have hf := hnone (idx w) (by omega)
    rw [cand_idx, (hs _).mp hw] at hf
    contradiction
  · exact Or.inr ⟨cand j, hout, (hs _).mpr hyes⟩

end PEqualNP.Outside
