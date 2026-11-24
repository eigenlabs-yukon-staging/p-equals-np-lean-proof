import PEqualNP.Outside.SparsePruningAlgorithm
import PEqualNP.Outside.DisjunctiveHardImage
import PEqualNP.Library.Machines.ReduceNP

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

private theorem imageLength_poly {f : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    ∃ r : Polynomial Nat, ∀ x y : List Bool, (f (x, y)).length ≤ r.eval (x.length + y.length) := by
  obtain ⟨r, hr⟩ := PEqualNP.Library.Machines.output_length_poly (fun s => f (unpairB s))
    (cpt_comp cpt_unpairB hf)
  have h (x y : List Bool) : (f (x,y)).length ≤ r.eval (2 * (x.length + y.length) + 1) := by
    have ht := hr (pairB x y)
    rw [unpairB_pairB, pairB_length] at ht
    exact ht.trans (eval_mono r (by omega))
  refine ⟨r.comp (Polynomial.C 2 * Polynomial.X + 1), fun x y => ?_⟩
  simpa [Polynomial.eval_comp] using h x y

/-- A polynomially sparse NP-hard target implies that bounded-length frontiers of
any NP language admit polynomial-cardinality existential-preserving pruning. -/
theorem SparseHardFrontier (A B : Language Bool) (hA : A ∈ NP) (hB : NPHard B)
    (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset (List Bool)),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n) :
    ∃ (p : Polynomial Nat) (prune : Nat → List (List Bool) → List (List Bool)),
      ∀ (n : Nat) (xs : List (List Bool)), (∀ x ∈ xs, x.length ≤ n) →
        (prune n xs).Sublist xs ∧ (prune n xs).length ≤ p.eval n ∧
          ((∃ y ∈ prune n xs, y ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  obtain ⟨f, hf, hspec⟩ := DisjunctiveHardImage A B hA hB
  obtain ⟨r, hr⟩ := imageLength_poly hf
  let t := r.comp (Polynomial.C 2 * Polynomial.X)
  obtain ⟨run, hrun⟩ := SparsePruningAlgorithm (fun x y => f (x,y))
  refine ⟨q.comp t + 1, fun n => run (q.eval (t.eval n)), fun n xs hxs => ?_⟩
  have hp (x y : List Bool) (hx : x ∈ xs) (hy : y ∈ xs) :
      (f (x,y)).length ≤ t.eval n := by
    have hh := (hr x y).trans (eval_mono r (show x.length + y.length ≤ 2 * n from by
      have := hxs x hx
      have := hxs y hy
      omega))
    simpa [t, Polynomial.eval_comp] using hh
  have hSparse (x : List Bool) (hx : x ∈ xs) (ys : Finset (List Bool))
      (hy : ∀ y ∈ ys, y ∈ B ∧ ∃ w ∈ xs, f (x,w) = y) : ys.card ≤ q.eval (t.eval n) := by
    apply sparse (t.eval n) ys
    intro y hys
    obtain ⟨hB, w, hw, rfl⟩ := hy y hys
    exact ⟨hB, hp x w hx hw⟩
  simpa [Polynomial.eval_comp] using
    hrun A B hspec (q.eval (t.eval n)) xs hSparse

end PEqualNP.Outside
