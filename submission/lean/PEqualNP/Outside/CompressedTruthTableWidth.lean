import PEqualNP.Outside.CompressedVariableTruthBoundary

namespace PEqualNP.Outside

private theorem ratio_bound (b k : Nat) :
    compressedTTBound b k ≤ 2^k * ttBound b k := by
  induction k with
  | zero => simp [compressedTTBound, ttBound]
  | succ k ih =>
    have hp : 1 ≤ 2^(k+1) := Nat.one_le_pow _ _ (by decide)
    calc
      compressedTTBound b (k+1) = 4 * ((k+1)*b) * compressedTTBound b k + 1 := by
        simp only [compressedTTBound]
        ring
      _ ≤ 4 * ((k+1)*b) * (2^k * ttBound b k) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ ≤ 4 * ((k+1)*b) * (2^k * ttBound b k) + 2^(k+1) :=
        Nat.add_le_add_left hp _
      _ = 2^(k+1) * ttBound b (k+1) := by
        simp only [ttBound, pow_succ]
        ring

private theorem exponent_bound (k : Nat) : k ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
    simp only [pow_succ]
    omega

private theorem recurrence_eq (b k : Nat) :
    compressedTTBound b k = Nat.rec 1 (fun i m => 2 * ((i+1) * b * (2*m)) + 1) k ∧
    ttBound b k = Nat.rec 1 (fun i m => 2 * ((i+1) * b * m) + 1) k := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨h₀,h₁⟩ := ih
    simp [compressedTTBound,ttBound,h₀,h₁]

/-- Directed trimming replaces the doubly exponential table-count multiplier
by an exponential factor in a fixed-width frontier bound. -/
theorem CompressedTruthTableWidth (b k : Nat) :
    let new := Nat.rec 1 (fun i m => 2 * ((i+1) * b * (2*m)) + 1) k
    let fixed := Nat.rec 1 (fun i m => 2 * ((i+1) * b * m) + 1) k
    new ≤ 2^k * fixed ∧ new ≤ (2^(2^k)) * fixed := by
  obtain ⟨h₀,h₁⟩ := recurrence_eq b k
  dsimp only
  rw [← h₀, ← h₁]
  refine ⟨ratio_bound b k, (ratio_bound b k).trans ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (exponent_bound k))

end PEqualNP.Outside
