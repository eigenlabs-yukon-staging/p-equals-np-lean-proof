import PEqualNP.Outside.PolynomialWitnessSearch

namespace PEqualNP.Outside

open PEqualNP.Library

/-- A verifier that characterizes the language and has at least one logarithmically short
certificate for each yes-input already yields a deterministic polynomial-time decider. -/
theorem LogWitnessCollapse (L : Language Bool) (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) (k : Nat)
    (characterizes : ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x, w) ∈ R)
    (short : ∀ x : List Bool, x ∈ L →
      ∃ w : List Bool, (x, w) ∈ R ∧ w.length ≤ k * (x.length + 1).log2) :
    L ∈ P := by
  let p : Polynomial Nat := Polynomial.C 2 * (Polynomial.X + 1) ^ k
  have hCover (x : List Bool) (hx : ∃ w : List Bool, (x, w) ∈ R) :
      ∃ w : List Bool, (x, w) ∈ R ∧ 2 ^ (w.length + 1) ≤ p.eval x.length + 1 := by
    obtain ⟨w, hw, hlen⟩ := short x ((characterizes x).mpr hx)
    refine ⟨w, hw, ?_⟩
    have hb : 2 ^ (x.length + 1).log2 ≤ x.length + 1 := Nat.log2_self_le (by omega)
    have hpow : 2 ^ w.length ≤ (x.length + 1) ^ k := calc
      2 ^ w.length ≤ 2 ^ (k * (x.length + 1).log2) := Nat.pow_le_pow_right (by decide) hlen
      _ = (2 ^ (x.length + 1).log2) ^ k := by rw [Nat.mul_comm k, pow_mul]
      _ ≤ (x.length + 1) ^ k := Nat.pow_le_pow_left hb _
    have hp : p.eval x.length = 2 * (x.length + 1) ^ k := by simp [p]
    rw [hp, pow_succ, Nat.mul_comm (2 ^ w.length)]
    exact (Nat.mul_le_mul_left 2 hpow).trans (Nat.le_add_right _ _)
  have heq : L = ({x : List Bool | ∃ w : List Bool, (x, w) ∈ R} : Language Bool) :=
    Set.ext characterizes
  rw [heq]
  exact PolynomialWitnessSearch R hR p hCover

end PEqualNP.Outside
