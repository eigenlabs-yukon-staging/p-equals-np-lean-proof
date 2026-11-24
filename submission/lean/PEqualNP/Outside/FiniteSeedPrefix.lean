import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace PEqualNP.Outside.FiniteSeedPrefix

def takeRows {α : Type} {k m : ℕ} (h : k ≤ m) (f : Fin m → α) : Fin k → α :=
  fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

def suffix {α : Type} {k m : ℕ} (h : k ≤ m) (f : Fin m → α) : Fin (m-k) → α :=
  fun i => f ⟨k + i.val, by omega⟩

def split {α : Type} {k m : ℕ} (h : k ≤ m) :
    (Fin m → α) ≃ ((Fin k → α) × (Fin (m-k) → α)) where
  toFun f := (takeRows h f, suffix h f)
  invFun g i := if hi : i.val < k then g.1 ⟨i.val, hi⟩ else g.2 ⟨i.val-k, by omega⟩
  left_inv f := by
    funext i
    dsimp only
    by_cases hi : i.val < k
    · simp [hi, takeRows]
    · rw [dif_neg hi]
      unfold suffix
      congr 1
      apply Fin.ext
      simp
      omega
  right_inv g := by
    apply Prod.ext
    · funext i
      simp [takeRows, i.isLt]
    · funext i
      have hi : ¬ k + i.val < k := by omega
      simp [suffix, hi]

def fibreEquiv {α : Type} {k m : ℕ} (h : k ≤ m) (p : (Fin k → α) → Prop) :
    {f : Fin m → α // p (takeRows h f)} ≃ ({g : Fin k → α // p g} × (Fin (m-k) → α)) where
  toFun f := (⟨takeRows h f.val, f.property⟩, suffix h f.val)
  invFun g := ⟨(split h).symm (g.1.val,g.2), by
    have he := congrArg Prod.fst ((split h).apply_symm_apply (g.1.val,g.2))
    change takeRows h ((split h).symm (g.1.val,g.2)) = g.1.val at he
    exact he.symm ▸ g.1.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (split h).left_inv f.val
  right_inv g := by
    have he := (split h).apply_symm_apply (g.1.val,g.2)
    have h₁ := congrArg (fun v : (Fin k → α) × (Fin (m-k) → α) => v.1) he
    have h₂ := congrArg (fun v : (Fin k → α) × (Fin (m-k) → α) => v.2) he
    exact Prod.ext (Subtype.ext h₁) h₂

theorem count_prefix {α : Type} [Fintype α] {k m : ℕ} (h : k ≤ m)
    (p : (Fin k → α) → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin m → α)).filter (fun f => p (takeRows h f))).card =
      ((Finset.univ : Finset (Fin k → α)).filter p).card * Fintype.card (Fin (m-k) → α) := by
  repeat rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fibreEquiv h p), Fintype.card_prod]

theorem count_total {α : Type} [Fintype α] {k m : ℕ} (h : k ≤ m) :
    Fintype.card (Fin m → α) = Fintype.card (Fin k → α) * Fintype.card (Fin (m-k) → α) := by
  rw [Fintype.card_congr (split h), Fintype.card_prod]

theorem lift_probability {α : Type} [Fintype α] {k m : ℕ} (h : k ≤ m)
    (p : (Fin k → α) → Prop) (q : (Fin m → α) → Prop) [DecidablePred p] [DecidablePred q] (c : ℕ)
    (hp : Fintype.card (Fin k → α) ≤ c * ((Finset.univ : Finset (Fin k → α)).filter p).card)
    (hq : ∀ f, p (takeRows h f) → q f) :
    Fintype.card (Fin m → α) ≤ c * ((Finset.univ : Finset (Fin m → α)).filter q).card := by
  rw [count_total (α := α) h]
  calc
    _ ≤ (c * ((Finset.univ : Finset (Fin k → α)).filter p).card) *
        Fintype.card (Fin (m-k) → α) := Nat.mul_le_mul_right _ hp
    _ = c * ((Finset.univ : Finset (Fin m → α)).filter (fun f => p (takeRows h f))).card := by
      rw [count_prefix h p, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card (by
      intro f hf
      obtain ⟨hm, hv⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨hm, hq f hv⟩))

end PEqualNP.Outside.FiniteSeedPrefix
