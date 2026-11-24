import PEqualNP.Outside.CompressedVariableTruthBoundary

namespace PEqualNP.Outside

private theorem ratio_bound (b k : Nat) :
    compressedTTBound b k ≤ (2*4^k) * ttBound b k := by
  induction k with
  | zero => simp [compressedTTBound, ttBound]
  | succ k ih =>
    have hp : 1 ≤ 4^k := Nat.one_le_pow _ _ (by decide)
    calc
      compressedTTBound b (k+1) = 8 * ((k+1)*b) * compressedTTBound b k + 2 := by
        simp only [compressedTTBound]
        ring
      _ ≤ 8 * ((k+1)*b) * ((2*4^k) * ttBound b k) + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ ≤ 8 * ((k+1)*b) * ((2*4^k) * ttBound b k) + 8 * 4^k :=
        Nat.add_le_add_left (by omega) _
      _ = (2*4^(k+1)) * ttBound b (k+1) := by
        simp only [ttBound, pow_succ]
        ring

private theorem exponent_bound (k : Nat) (hk : 3 ≤ k) : 1 + 2*k ≤ 2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 3 ≤ k
    · have hi := ih h
      simp only [pow_succ]
      omega
    · have he : k = 2 := by omega
      subst k
      decide

private theorem recurrence_eq (b k : Nat) :
    compressedTTBound b k = Nat.rec 2 (fun i m => 2 * (2 * ((i+1) * b * (2*m)) + 1)) k ∧
    ttBound b k = Nat.rec 1 (fun i m => 2 * ((i+1) * b * m) + 1) k := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨h₀,h₁⟩ := ih
    simp [compressedTTBound,ttBound,h₀,h₁]

/-- The two-bucket construction avoids the doubly exponential count of distinct
tables in the width bound, and its bound is no larger starting at arity three. -/
theorem CompressedTruthTableWidth (b k : Nat) :
    let new := Nat.rec 2 (fun i m => 2 * (2 * ((i+1) * b * (2*m)) + 1)) k
    let fixed := Nat.rec 1 (fun i m => 2 * ((i+1) * b * m) + 1) k
    new ≤ (2 * 4^k) * fixed ∧
      (3 ≤ k → new ≤ (2^(2^k)) * fixed) := by
  obtain ⟨h₀,h₁⟩ := recurrence_eq b k
  dsimp only
  rw [← h₀, ← h₁]
  refine ⟨ratio_bound b k, fun hk => (ratio_bound b k).trans ?_⟩
  apply Nat.mul_le_mul_right
  have he : 2 * 4^k = 2^(1 + 2*k) := by rw [pow_add, pow_mul]; rfl
  rw [he]
  exact Nat.pow_le_pow_right (by decide) (exponent_bound k hk)

end PEqualNP.Outside
