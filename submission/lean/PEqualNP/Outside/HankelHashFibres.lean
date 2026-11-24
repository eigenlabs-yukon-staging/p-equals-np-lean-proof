import PEqualNP.Outside.HankelHashSurjective

namespace PEqualNP.Outside.HankelHash

def eval {n k : ℕ} (s : Hankel n k × Vec k) (x : Vec n) : Vec k :=
  applyMatrix s.1 x + s.2

def hit {n k : ℕ} (s : Hankel n k × Vec k) (x : Vec n) : Prop :=
  eval s x = 0

instance {n k : ℕ} (s : Hankel n k × Vec k) (x : Vec n) : Decidable (hit s x) := by
  unfold hit
  infer_instance

theorem matrix_sub {n k : ℕ} (s : Hankel n k) (x y : Vec n) :
    applyMatrix s (x-y) = applyMatrix s x - applyMatrix s y := by
  funext i
  simp [applyMatrix,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

def matrixAdd {n k : ℕ} (x : Vec n) : Hankel n k →+ Vec k where
  toFun s := applyMatrix s x
  map_zero' := by funext i; simp [applyMatrix]
  map_add' a b := by funext i; simp [applyMatrix,Pi.add_apply,add_mul,Finset.sum_add_distrib]

noncomputable def splitSurj {α β : Type} [AddGroup α] [AddGroup β]
    (f : α →+ β) (h : Function.Surjective f) : ({a : α // f a = 0} × β) ≃ α := by
  let r (b : β) := Classical.choose (h b)
  have hr (b : β) : f (r b) = b := Classical.choose_spec (h b)
  exact
    { toFun := fun a => a.1.1 + r a.2
      invFun := fun a => (⟨a - r (f a), by rw [map_sub,hr,sub_self]⟩, f a)
      left_inv := by
        rintro ⟨⟨a,ha⟩,b⟩
        have he : f (a+r b) = b := by rw [map_add,ha,hr,zero_add]
        apply Prod.ext
        · apply Subtype.ext
          change a+r b-r (f (a+r b)) = a
          rw [he,add_sub_cancel_right]
        · exact he
      right_inv := fun a => sub_add_cancel a _ }

def singleEquiv {n k : ℕ} (x : Vec n) :
    {s : Hankel n k × Vec k // hit s x} ≃ Hankel n k where
  toFun s := s.1.1
  invFun a := ⟨(a,-applyMatrix a x),add_neg_cancel _⟩
  left_inv := by
    rintro ⟨⟨a,b⟩,hb⟩
    change applyMatrix a x + b = 0 at hb
    apply Subtype.ext
    change (a, -applyMatrix a x) = (a,b)
    refine Prod.ext (show a = a from rfl) ?_
    change -applyMatrix a x = b
    calc
      -applyMatrix a x = -applyMatrix a x + (applyMatrix a x + b) := by rw [hb,add_zero]
      _ = b := by abel
  right_inv _ := rfl

def jointEquiv {n k : ℕ} (x y : Vec n) :
    {s : Hankel n k × Vec k // hit s x ∧ hit s y} ≃
      {a : Hankel n k // matrixAdd (k := k) (x-y) a = 0} where
  toFun s := ⟨s.1.1, by
    change applyMatrix s.1.1 (x-y) = 0
    rw [matrix_sub,sub_eq_zero]
    have hx : applyMatrix s.1.1 x + s.1.2 = 0 := s.2.1
    have hy : applyMatrix s.1.1 y + s.1.2 = 0 := s.2.2
    exact add_right_cancel (hx.trans hy.symm)⟩
  invFun a := ⟨(a.1,-applyMatrix a.1 x),by
    have he : applyMatrix a.1 (x-y) = 0 := a.2
    rw [matrix_sub,sub_eq_zero] at he
    exact ⟨add_neg_cancel _,by change applyMatrix a.1 y + -applyMatrix a.1 x = 0; rw [← he,add_neg_cancel]⟩⟩
  left_inv := by
    intro s
    apply Subtype.ext
    have h := congrArg Subtype.val ((singleEquiv x).left_inv ⟨s.1,s.2.1⟩)
    exact h
  right_inv _ := rfl

theorem card_fibres {n k : ℕ} (x y : Vec n) (hxy : x ≠ y) :
    (Fintype.card {s : Hankel n k × Vec k // hit s x} = 2^(n+k)) ∧
    (2^k * Fintype.card {s : Hankel n k × Vec k // hit s x ∧ hit s y} = 2^(n+k)) := by
  have hs := Fintype.card_congr (singleEquiv (k := k) x)
  have hj := Fintype.card_congr (jointEquiv (k := k) x y)
  have he := Fintype.card_congr (splitSurj (matrixAdd (k := k) (x-y))
    (matrix_surjective (x-y) (sub_ne_zero.mpr hxy)))
  have hv (m : ℕ) : Fintype.card (Vec m) = 2^m := by simp [Vec,Coord,ZMod.card]
  constructor
  · rw [hs]
    exact hv _
  · rw [hj]
    rw [Fintype.card_prod,hv] at he
    rw [Nat.mul_comm]
    exact he.trans (hv _)

end PEqualNP.Outside.HankelHash
