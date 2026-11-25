import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

namespace PEqualNP.Outside

private def load (n : ℕ) (xs : List ℕ) : ℕ :=
  ((List.range xs.length).map (fun i => ((xs.drop i).take n).sum)).sum

private theorem load_cons (n x : ℕ) (xs : List ℕ) :
    load n (x::xs) = ((x::xs).take n).sum + load n xs := by
  simp only [load,List.length_cons,List.range_succ_eq_map,List.map_cons,List.drop_zero,
    List.map_map,List.sum_cons,Function.comp_def,List.drop_succ_cons]

private theorem load_from_head (n : ℕ) (xs : List ℕ) :
    ((xs.take n).sum + load n xs.tail) = load n xs := by
  cases xs with
  | nil => simp [load]
  | cons x xs => exact (load_cons n x xs).symm

private theorem load_succ (n : ℕ) (xs : List ℕ) :
    load (n+1) xs = xs.sum + load n xs.tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [load_cons,List.take_succ_cons,ih]
    change x + (xs.take n).sum + (xs.sum + load n xs.tail) = x + xs.sum + load n xs
    rw [← load_from_head n xs]
    omega

private theorem load_bound (n : ℕ) (xs : List ℕ) : load n xs ≤ n*xs.sum := by
  induction n generalizing xs with
  | zero => simp [load]
  | succ n ih =>
    rw [load_succ,Nat.add_mul,Nat.one_mul]
    have ht : xs.tail.sum ≤ xs.sum := by cases xs <;> simp
    have h := (ih xs.tail).trans (Nat.mul_le_mul_left n ht)
    omega

/-- Over all bounded contiguous windows of a finite sequence, each item
contributes its nonnegative weight at most once per possible window offset. -/
theorem WindowWeightBound (n : ℕ) (weights : List ℕ) :
    ((List.range weights.length).map (fun i => ((weights.drop i).take n).sum)).sum ≤ n * weights.sum :=
  load_bound n weights

end PEqualNP.Outside
