import PEqualNP.Outside.SparseHardImpliesCollapse

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

theorem sparseCumulativeOfPointwise (B : Language Bool) (q : Polynomial Nat)
    (hs : ∀ (n : Nat) (ys : Finset (List Bool)),
      (∀ y ∈ ys, y ∈ B ∧ y.length = n) → ys.card ≤ q.eval n) :
    ∀ (n : Nat) (ys : Finset (List Bool)),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) →
        ys.card ≤ ((Polynomial.X + 1) * q).eval n := by
  classical
  intro n ys hy
  let lengths := Finset.range (n + 1)
  have hmap (x : List Bool) (hx : x ∈ ys) : x.length ∈ lengths :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hy x hx).2)
  rw [Finset.card_eq_sum_card_fiberwise hmap, Polynomial.eval_mul]
  have hb (i : Nat) (hi : i ∈ lengths) :
      (ys.filter (fun x => x.length = i)).card ≤ q.eval n := by
    have h₁ : (ys.filter (fun x => x.length = i)).card ≤ q.eval i := by
      apply hs i
      intro x hx
      obtain ⟨hm, he⟩ := Finset.mem_filter.mp hx
      exact ⟨(hy x hm).1, he⟩
    have h₂ : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact h₁.trans (eval_mono q h₂)
  calc
    _ ≤ ∑ _i ∈ lengths, q.eval n := Finset.sum_le_sum hb
    _ = (Polynomial.X + 1 : Polynomial Nat).eval n * q.eval n := by simp [lengths]

theorem singleton_hard_of_collapse (h : P = NP) :
    NPHard ({[]} : Language Bool) := by
  intro A hA
  have hP : A ∈ P := h ▸ hA
  obtain ⟨decideA, spec, hc⟩ := hP
  let f := fun x : List Bool => sel (bflag (decideA x)) [true] []
  refine ⟨f, cpt_sel (cpt_bitFlag hc) (cpt_const [true]) (cpt_const []), fun x => ?_⟩
  refine (spec x).trans ?_
  change decideA x = true ↔ f x = []
  cases he : decideA x <;> simp [f, he, bflag]

/-- The reference P versus NP collapse is equivalent to the existence of a polynomially
sparse NP-hard target, using the ordinary exact-length definition of sparsity. -/
theorem CollapseIffSparseHard :
    P = NP ↔ ∃ (B : Language Bool) (q : Polynomial Nat), NPHard B ∧
      ∀ (n : Nat) (ys : Finset (List Bool)),
        (∀ y ∈ ys, y ∈ B ∧ y.length = n) → ys.card ≤ q.eval n := by
  constructor
  · intro h
    refine ⟨({[]} : Language Bool), 1, singleton_hard_of_collapse h, fun n ys hy => ?_⟩
    have hsub : ys ⊆ ({[]} : Finset (List Bool)) := by
      intro y hmem
      have hh := (hy y hmem).1
      exact Finset.mem_singleton.mpr (show y = [] from hh)
    simpa using Finset.card_le_card hsub
  · rintro ⟨B, q, hB, hs⟩
    exact SparseHardImpliesCollapse B hB ((Polynomial.X + 1) * q) (sparseCumulativeOfPointwise B q hs)

end PEqualNP.Outside
