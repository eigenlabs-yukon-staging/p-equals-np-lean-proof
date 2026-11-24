import PEqualNP.Outside.CompressedVariableTruthBoundary

namespace PEqualNP.Outside

local notation "Word" => List Bool

private theorem power_cap (b k : Nat) : compressedTTBound b k ≤ (4*k*b+1)^k := by
  let base := 4*k*b+1
  have hb : 0 < base := by simp [base]
  have H : ∀ j : Nat, j ≤ k → compressedTTBound b j ≤ base^j := by
    intro j hj
    induction j with
    | zero => simp [compressedTTBound]
    | succ j ih =>
      have hp : 1 ≤ base^j := Nat.one_le_pow _ _ hb
      have hmul : 4*(j+1)*b ≤ 4*k*b :=
        Nat.mul_le_mul_right b (Nat.mul_le_mul_left 4 hj)
      calc
        compressedTTBound b (j+1) = (4*(j+1)*b)*compressedTTBound b j + 1 := by
          simp only [compressedTTBound]
          ring
        _ ≤ (4*k*b)*base^j + base^j :=
          Nat.add_le_add (Nat.mul_le_mul hmul (ih (by omega))) hp
        _ = base^(j+1) := by simp only [base,pow_succ]; ring
  exact H k le_rfl

private theorem natural_le_two_pow (i : Nat) : i ≤ 2^i := by
  induction i with
  | zero => decide
  | succ i ih =>
    have hp : 1 ≤ 2^i := Nat.one_le_pow _ _ (by decide)
    simp only [pow_succ]
    omega

private theorem log_width (n a k b : Nat)
    (hk : k ≤ (n+1).log2+1) (hb : b ≤ (n+1)^a) :
    compressedTTBound b k ≤ 2^((a+4)*((n+1).log2+1)^2) := by
  let ℓ := (n+1).log2+1
  have hℓ : 1 ≤ ℓ := by simp [ℓ]
  have hn : n+1 ≤ 2^ℓ :=
    ((Nat.log2_lt (n := n+1) (by omega)).mp (by simp [ℓ])).le
  have hb' : b ≤ 2^(ℓ*a) :=
    hb.trans (by rw [pow_mul]; exact Nat.pow_le_pow_left hn a)
  have hk' : k ≤ 2^ℓ := hk.trans (natural_le_two_pow ℓ)
  have hsmall : 4*k*b ≤ 2^(2+ℓ+ℓ*a) := by
    rw [pow_add,pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul (by decide) hk') hb'
  have hone : 1 ≤ 2^(2+ℓ+ℓ*a) := Nat.one_le_pow _ _ (by decide)
  have hbase : 4*k*b+1 ≤ 2^((a+4)*ℓ) := by
    calc
      4*k*b+1 ≤ 2^(2+ℓ+ℓ*a) + 2^(2+ℓ+ℓ*a) := Nat.add_le_add hsmall hone
      _ = 2^((2+ℓ+ℓ*a)+1) := by simp [pow_succ,Nat.mul_two]
      _ ≤ 2^((a+4)*ℓ) := by
        apply Nat.pow_le_pow_right (by decide)
        calc
          2+ℓ+ℓ*a+1 = a*ℓ+ℓ+3 := by ring
          _ ≤ a*ℓ+ℓ+3*ℓ := by omega
          _ = (a+4)*ℓ := by ring
  calc
    compressedTTBound b k ≤ (4*k*b+1)^k := power_cap b k
    _ ≤ (2^((a+4)*ℓ))^k := Nat.pow_le_pow_left hbase k
    _ = 2^((a+4)*ℓ*k) := by exact (pow_mul 2 ((a+4)*ℓ) k).symm
    _ ≤ 2^((a+4)*ℓ^2) := by
      apply Nat.pow_le_pow_right (by decide)
      rw [pow_two,← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hk

/-- The directed pruner retains a quasipolynomially bounded frontier when the
query arity is logarithmic and the sparse membership budget is polynomial.
This theorem bounds list width, independently of the cost of uniform compilation. -/
theorem CompressedTruthTableLogarithmicWidth (n a k b : Nat)
    (hk : k ≤ (n+1).log2+1) (hb : b ≤ (n+1)^a)
    (q : Word → Fin k → Word) (t : Word → (Fin k → Bool) → Bool) :
    ∃ thin : List Word → List Word,
      ∀ xs : List Word, xs.Nodup →
        (thin xs).Sublist xs ∧ (thin xs).length ≤ 2^((a+4)*((n+1).log2+1)^2) ∧
        ∀ (S : Finset Word) (l r : List Word) (w : Word),
          S.card ≤ b → xs = l ++ w::r →
          (∀ x ∈ l ++ [w], t x (fun i => decide (q x i ∈ S)) = true) →
          (∀ x ∈ r, t x (fun i => decide (q x i ∈ S)) = false) →
          w ∈ thin xs := by
  refine ⟨keepCompressedBoundary k b q t,fun xs hn => ?_⟩
  obtain ⟨hsub,hlen,hkeep⟩ := compressedBoundarySpec k b q t xs hn
  exact ⟨hsub,hlen.trans (log_width n a k b hk hb),
    fun S l r w hS hs h₁ h₂ => hkeep S w hS ⟨l,r,hs,h₁,h₂⟩⟩

end PEqualNP.Outside
