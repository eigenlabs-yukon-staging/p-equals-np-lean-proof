import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.HankelHash
abbrev Coord := ZMod 2
abbrev Vec (n : ℕ) := Fin n → Coord

abbrev Hankel (n k : ℕ) := Vec (n+k)

def applyMatrix {n k : ℕ} (s : Hankel n k) (x : Vec n) : Vec k :=
  fun i => ∑ j : Fin n, s ⟨i.val+j.val, by have := i.isLt; have := j.isLt; omega⟩ * x j

theorem last_nonzero {n : ℕ} (d : Vec n) (hnz : d ≠ 0) :
    ∃ j : Fin n, d j = 1 ∧ ∀ l : Fin n, j < l → d l = 0 := by
  let S := (Finset.univ : Finset (Fin n)).filter (fun j => d j ≠ 0)
  have Sne : S.Nonempty := by
    by_contra h
    apply hnz
    funext j
    change d j = 0
    by_contra hj
    exact h ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let j := S.max' Sne
  have hj : d j ≠ 0 := (Finset.mem_filter.mp (S.max'_mem Sne)).2
  have hcoord : ∀ a : Coord, a ≠ 0 → a = 1 := by decide
  refine ⟨j, hcoord (d j) hj, ?_⟩
  intro l hl
  by_contra h
  have hm : l ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  exact (not_le_of_gt hl) (S.le_max' l hm)

def sequenceEval {n : ℕ} (s : ℕ → Coord) (d : Vec n) (i : ℕ) : Coord :=
  ∑ j : Fin n, s (i+j.val) * d j

theorem solve_prefix {n : ℕ} (d : Vec n) (b : ℕ → Coord) (p : Fin n)
    (hp : d p = 1) (hmax : ∀ j : Fin n, p < j → d j = 0) :
    ∀ k : ℕ, ∃ s : ℕ → Coord, ∀ i < k, sequenceEval s d i = b i := by
  intro k
  induction k with
  | zero => exact ⟨fun _ => 0, fun i hi => by omega⟩
  | succ k ih =>
    obtain ⟨s,hs⟩ := ih
    let delta := b k - sequenceEval s d k
    let t i := s i + if i = k+p.val then delta else 0
    refine ⟨t, ?_⟩
    intro i hi
    have hsplit : sequenceEval t d i = sequenceEval s d i +
        ∑ j : Fin n, (if i+j.val = k+p.val then delta else 0) * d j := by
      simp only [sequenceEval,t,add_mul,Finset.sum_add_distrib]
    rw [hsplit]
    by_cases hik : i = k
    · subst i
      rw [Finset.sum_eq_single p]
      · simp [hp,delta]
      · intro j _ hj
        have he : k+j.val ≠ k+p.val := by
          intro h
          exact hj (Fin.ext (by omega))
        rw [ite_eq_right he,zero_mul]
      · simp
    · have hs' := hs i (by omega)
      rw [hs']
      suffices hsum : ∑ j : Fin n, (if i+j.val = k+p.val then delta else 0) * d j = 0 by
        rw [hsum,add_zero]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : i+j.val = k+p.val
      · have hj' : p < j := by change p.val < j.val; omega
        simp [hmax j hj']
      · simp [hj]

theorem matrix_surjective {n k : ℕ} (d : Vec n) (hd : d ≠ 0) :
    Function.Surjective (fun s : Hankel n k => applyMatrix s d) := by
  intro b
  obtain ⟨p,hp,hmax⟩ := last_nonzero d hd
  let T (i : ℕ) : Coord := if h : i < k then b ⟨i,h⟩ else 0
  obtain ⟨s,hs⟩ := solve_prefix d T p hp hmax k
  refine ⟨fun i => s i.val, funext fun i => ?_⟩
  exact (hs i.val i.isLt).trans (dite_eq_left i.isLt)

end PEqualNP.Outside.HankelHash

theorem PEqualNP.Outside.HankelHashSurjective :
    ∀ (n k : ℕ) (d : Fin n → ZMod 2), d ≠ 0 →
      ∀ b : Fin k → ZMod 2, ∃ s : Fin (n+k) → ZMod 2,
        ∀ i : Fin k, (∑ j : Fin n, s ⟨i.val+j.val,
          Nat.lt_of_lt_of_le (Nat.add_lt_add i.isLt j.isLt) (Nat.le_of_eq (Nat.add_comm k n))⟩ * d j) = b i := by
  intro n k d hd b
  obtain ⟨s,hs⟩ := PEqualNP.Outside.HankelHash.matrix_surjective d hd b
  exact ⟨s,congrFun hs⟩
