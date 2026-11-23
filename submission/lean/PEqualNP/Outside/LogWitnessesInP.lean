import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Outside.DecideFromWitnessSearch

open PEqualNP.Library PEqualNP.Outside.BoundedEnumeration

theorem PEqualNP.Outside.LogWitnessesInP
    (L : Language Bool) (R : Set (List Bool × List Bool)) (p : Polynomial ℕ) (c d : ℕ)
    (hR : DecidableInPolyTime encodePair R)
    (hL : ∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R)
    (hshort : ∀ x ∈ L, ∃ w : List Bool,
      w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧ w.length ≤ c * Nat.log2 (x.length + 1) + d) :
    L ∈ P := by
  let budget : Polynomial ℕ := Polynomial.C (2 ^ (d + 1)) * (Polynomial.X + 1) ^ c
  obtain ⟨s, hs, hsel⟩ := EnumeratingSelector.select_bounded R p budget hR
  apply DecideFromWitnessSearch L R p s hR hs hL
  intro x hx
  obtain ⟨w, hb, hrel, hlen⟩ := hshort x hx
  refine hsel x ⟨w, ⟨hb, hrel⟩, ?_⟩
  have hpow : 2 ^ Nat.log2 (x.length + 1) ≤ x.length + 1 :=
    (Nat.le_log2 (by omega : x.length + 1 ≠ 0)).mp le_rfl
  have hidx := idx_lt_of_length_le hlen
  have hg : 2 ^ (c * Nat.log2 (x.length + 1) + d + 1) ≤
      2 ^ (d + 1) * (x.length + 1) ^ c := by
    rw [Nat.add_assoc, pow_add, Nat.mul_comm c, pow_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow c)
  simp only [budget, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  exact (Nat.le_add_right _ _).trans (hidx.trans hg)
