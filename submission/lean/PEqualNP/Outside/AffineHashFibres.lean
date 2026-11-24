import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace PEqualNP.Outside.AffineHash

abbrev Coord := ZMod 2
abbrev Vec (n : ℕ) := Fin n → Coord
abbrev Row (n : ℕ) := Vec n × Coord
abbrev Seed (n k : ℕ) := Fin k → Row n

def dot {n : ℕ} (a x : Vec n) : Coord := ∑ i, a i * x i

def rowEval {n : ℕ} (r : Row n) (x : Vec n) : Coord := dot r.1 x + r.2

def hit {n k : ℕ} (h : Seed n k) (x : Vec n) : Prop := ∀ i, rowEval (h i) x = 0

instance {n k : ℕ} (h : Seed n k) (x : Vec n) : Decidable (hit h x) := by
  unfold hit
  infer_instance

theorem dot_sub_right {n : ℕ} (a x y : Vec n) :
    dot a (x - y) = dot a x - dot a y := by
  simp [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dot_add_left {n : ℕ} (a b x : Vec n) :
    dot (a + b) x = dot a x + dot b x := by
  simp [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_sub_left {n : ℕ} (a b x : Vec n) :
    dot (a - b) x = dot a x - dot b x := by
  simp [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

def scale {n : ℕ} (c : Coord) (v : Vec n) : Vec n := fun i => c * v i

theorem dot_scale_left {n : ℕ} (c : Coord) (a x : Vec n) :
    dot (scale c a) x = c * dot a x := by
  simp [dot, scale, Finset.mul_sum, mul_assoc]

def pivot {n : ℕ} (j : Fin n) : Vec n := fun i => if i = j then 1 else 0

theorem dot_pivot {n : ℕ} (j : Fin n) (x : Vec n) : dot (pivot j) x = x j := by
  unfold dot pivot
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

def singleRow {n : ℕ} (x : Vec n) :
    {r : Row n // rowEval r x = 0} ≃ Vec n where
  toFun r := r.val.1
  invFun a := ⟨(a, -dot a x), by exact add_neg_cancel _⟩
  left_inv := by
    rintro ⟨⟨a,b⟩, hb⟩
    apply Subtype.ext
    simp only [rowEval] at hb
    change (a, -dot a x) = (a,b)
    have he : -dot a x = b := by
      calc
        -dot a x = -dot a x + (dot a x + b) := by rw [hb, add_zero]
        _ = b := by abel
    rw [he]
  right_inv _ := rfl

def jointRow {n : ℕ} (x y : Vec n) :
    {r : Row n // rowEval r x = 0 ∧ rowEval r y = 0} ≃ {a : Vec n // dot a (x-y) = 0} where
  toFun r := ⟨r.val.1, by
    rw [dot_sub_right, sub_eq_zero]
    have hs := r.property
    simp only [rowEval] at hs
    exact add_right_cancel (hs.1.trans hs.2.symm)⟩
  invFun a := ⟨(a.val, -dot a.val x), by
    have h := a.property
    rw [dot_sub_right, sub_eq_zero] at h
    exact ⟨add_neg_cancel _, by change dot a.val y + -dot a.val x = 0; rw [← h, add_neg_cancel]⟩⟩
  left_inv := by
    intro r
    apply Subtype.ext
    have h := congrArg (fun q : {u : Row n // rowEval u x = 0} => q.val)
      ((singleRow x).left_inv ⟨r.val, r.property.1⟩)
    simpa only [singleRow] using h
  right_inv _ := rfl

def splitHyperplane {n : ℕ} (d : Vec n) (j : Fin n) (hj : d j = 1) :
    ({a : Vec n // dot a d = 0} × Coord) ≃ Vec n where
  toFun q := q.1.val + scale q.2 (pivot j)
  invFun a := (⟨a - scale (dot a d) (pivot j), by
    rw [dot_sub_left, dot_scale_left, dot_pivot, hj, mul_one, sub_self]⟩, dot a d)
  left_inv := by
    rintro ⟨⟨a, ha⟩, c⟩
    have h : dot (a + scale c (pivot j)) d = c := by
      rw [dot_add_left, ha, dot_scale_left, dot_pivot, hj, mul_one, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change a + scale c (pivot j) - scale (dot (a + scale c (pivot j)) d) (pivot j) = a
      rw [h, add_sub_cancel_right]
    · exact h
  right_inv a := sub_add_cancel a _

theorem neq_pivot {n : ℕ} (x y : Vec n) (h : x ≠ y) :
    ∃ j : Fin n, (x-y) j = 1 := by
  have he : ∃ j, x j ≠ y j := by
    by_contra hn
    push Not at hn
    exact h (funext hn)
  obtain ⟨j, hj⟩ := he
  refine ⟨j, ?_⟩
  have hn : x j - y j ≠ 0 := sub_ne_zero.mpr hj
  have hone : ∀ t : Coord, t ≠ 0 → t = 1 := by decide
  exact hone _ hn

def coordinatewise {n k : ℕ} (p : Row n → Prop) :
    {h : Seed n k // ∀ i, p (h i)} ≃ (Fin k → {r : Row n // p r}) where
  toFun h i := ⟨h.val i, h.property i⟩
  invFun v := ⟨fun i => (v i).val, fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv v := funext fun i => Subtype.ext rfl

theorem card_single {n k : ℕ} (x : Vec n) :
    Fintype.card {h : Seed n k // hit h x} = (Fintype.card (Vec n)) ^ k := by
  classical
  have e : {h : Seed n k // hit h x} ≃ (Fin k → {r : Row n // rowEval r x = 0}) :=
    coordinatewise (n := n) (k := k) (fun r => rowEval r x = 0)
  rw [Fintype.card_congr e]
  simp [Fintype.card_congr (singleRow x)]

theorem card_joint {n k : ℕ} (x y : Vec n) :
    Fintype.card {h : Seed n k // hit h x ∧ hit h y} =
      (Fintype.card {a : Vec n // dot a (x-y) = 0}) ^ k := by
  classical
  have e : {h : Seed n k // hit h x ∧ hit h y} ≃
      {h : Seed n k // ∀ i, rowEval (h i) x = 0 ∧ rowEval (h i) y = 0} :=
    Equiv.subtypeEquivRight (fun _ => forall_and.symm)
  rw [Fintype.card_congr e, Fintype.card_congr (coordinatewise (n := n) (k := k) (fun r => rowEval r x = 0 ∧ rowEval r y = 0))]
  simp [Fintype.card_congr (jointRow x y)]

theorem card_hyperplane {n : ℕ} (x y : Vec n) (h : x ≠ y) :
    2 * Fintype.card {a : Vec n // dot a (x-y) = 0} = Fintype.card (Vec n) := by
  classical
  obtain ⟨j, hj⟩ := neq_pivot x y h
  have he := Fintype.card_congr (splitHyperplane (x-y) j hj)
  simpa [Fintype.card_prod, ZMod.card, Nat.mul_comm] using he

end PEqualNP.Outside.AffineHash
