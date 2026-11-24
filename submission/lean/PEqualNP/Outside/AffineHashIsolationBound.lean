import PEqualNP.Outside.AffineHashFibres
import PEqualNP.Outside.PairwiseIsolationCounting

namespace PEqualNP.Outside.AffineHash

theorem vec_card (n : ℕ) : Fintype.card (Vec n) = 2 ^ n := by
  simp [Vec, Coord, ZMod.card]

theorem seed_card (n k : ℕ) : Fintype.card (Seed n k) = 2 ^ k * (2 ^ n) ^ k := by
  simp [Seed, Row, Vec, Coord, ZMod.card, mul_pow, Nat.mul_comm]

theorem single_size {n k : ℕ} (x : Vec n) :
    ((Finset.univ : Finset (Seed n k)).filter (fun f => hit f x)).card = (2 ^ n) ^ k := by
  rw [← Fintype.card_subtype, card_single, vec_card]

theorem joint_size {n k : ℕ} (hn : 0 < n) (x y : Vec n) (hxy : x ≠ y) :
    ((Finset.univ : Finset (Seed n k)).filter (fun f => hit f x ∧ hit f y)).card =
      (2 ^ (n - 1)) ^ k := by
  rw [← Fintype.card_subtype, card_joint]
  have hv : Fintype.card {a : Vec n // dot a (x - y) = 0} = 2 ^ (n - 1) := by
    have h' := card_hyperplane x y hxy
    rw [vec_card] at h'
    have he : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_succ, Nat.mul_comm]
    omega
  rw [hv]

private theorem power_boundary {n : ℕ} (hn : 0 < n) : 2 * 2 ^ (n - 1) = 2 ^ n := by
  conv_rhs => rw [← Nat.sub_add_cancel hn]
  rw [pow_succ, Nat.mul_comm]

set_option maxHeartbeats 1500000 in
theorem bound_at_width {n k : ℕ} (hn : 0 < n) (S : Finset (Vec n))
    (hsmall : 2 * S.card ≤ 2 ^ k) (hlarge : 2 ^ k ≤ 4 * S.card) :
    Fintype.card (Seed n k) ≤ 8 *
      ((Finset.univ : Finset (Seed n k)).filter (fun f =>
        ∃ s ∈ S, hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)).card := by
  let p : ℕ := (2 ^ n) ^ k
  let q : ℕ := (2 ^ (n - 1)) ^ k
  let I := ((Finset.univ : Finset (Seed n k)).filter (fun f =>
    ∃ s ∈ S, hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)).card
  have hp : 2 ^ k * q = p := by
    unfold p q
    rw [← mul_pow, power_boundary hn]
  have hcount0 :=
    PEqualNP.Outside.PairwiseIsolation.count_bound (Finset.univ : Finset (Seed n k)) S (@hit n k) p q
      (fun s _ => single_size (k := k) s) (fun s _ t _ h => (joint_size (k := k) hn s t (Ne.symm h)).le)
  have heq : (PEqualNP.Outside.PairwiseIsolation.isolates (Finset.univ : Finset (Seed n k)) S hit).card = I := by
    unfold I
    congr 1
    ext f
    simp only [PEqualNP.Outside.PairwiseIsolation.isolates, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount : S.card * p ≤ I + S.card * ((S.card - 1) * q) := by
    rwa [heq] at hcount0
  have hpen : 2 * (S.card * ((S.card - 1) * q)) ≤ S.card * p := by
    have hs : 2 * (S.card - 1) ≤ 2 ^ k := by omega
    have hq := Nat.mul_le_mul_right q hs
    rw [hp] at hq
    calc
      2 * (S.card * ((S.card - 1) * q)) = S.card * ((2 * (S.card - 1)) * q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hq
  have hi : S.card * p ≤ 2 * I := by omega
  calc
    Fintype.card (Seed n k) = 2 ^ k * p := seed_card n k
    _ ≤ (4 * S.card) * p := Nat.mul_le_mul_right p hlarge
    _ = 4 * (S.card * p) := Nat.mul_assoc _ _ _
    _ ≤ 4 * (2 * I) := Nat.mul_le_mul_left 4 hi
    _ = 8 * I := by omega

theorem width_exists {n : ℕ} (S : Finset (Vec n)) (hs : S.Nonempty) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n + 2 ∧ 2 * S.card ≤ 2 ^ k ∧ 2 ^ k ≤ 4 * S.card := by
  have hcard : S.card ≤ 2 ^ n := by
    have h := Finset.card_le_univ S
    rwa [vec_card] at h
  have hpositive : S.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hs)
  let k := Nat.log2 S.card + 2
  have hu : Nat.log2 S.card ≤ n := by
    have he : S.card < 2 ^ (n + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ n := by positivity
      omega
    have hh := (Nat.log2_lt hpositive).mpr he
    omega
  have h₁ := Nat.lt_log2_self (n := S.card)
  have h₂ := Nat.log2_self_le hpositive
  refine ⟨k, by omega, by omega, ?_, ?_⟩
  · unfold k
    rw [show S.card.log2 + 2 = (S.card.log2 + 1) + 1 by omega, pow_succ]
    omega
  · unfold k
    rw [pow_add]
    norm_num
    omega

end PEqualNP.Outside.AffineHash

open PEqualNP.Outside.AffineHash in
theorem PEqualNP.Outside.AffineHashIsolationBound
    (n : ℕ) (hn : 0 < n) (S : Finset (Fin n → ZMod 2)) (hs : S.Nonempty) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n + 2 ∧
      Fintype.card (Fin k → ((Fin n → ZMod 2) × ZMod 2)) ≤ 8 *
        ((Finset.univ : Finset (Fin k → ((Fin n → ZMod 2) × ZMod 2))).filter (fun f =>
          ∃ s ∈ S, (∀ i, (∑ j : Fin n, (f i).1 j * s j) + (f i).2 = 0) ∧
            ∀ t ∈ S, t ≠ s → ¬ (∀ i, (∑ j : Fin n, (f i).1 j * t j) + (f i).2 = 0))).card := by
  obtain ⟨k, hk, hlarge, h₁, h₂⟩ := width_exists S hs
  exact ⟨k, hk, hlarge, bound_at_width hn S h₁ h₂⟩
