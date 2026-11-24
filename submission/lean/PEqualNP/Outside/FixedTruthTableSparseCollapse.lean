import PEqualNP.Outside.MeasuredBoundedTruthTableBoundary
import PEqualNP.Library.L010
import PEqualNP.Outside.OrderedSparseFrontierSolver

namespace PEqualNP.Outside

open TruthTableSolver

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Verifier" => Word × Word → Bool

theorem tuple_length_bound (k : Nat) (q : Word → Fin k → Word)
    (hq : ∀ i, CPT (fun x => q x i)) :
    ∃ r : Polynomial Nat, ∀ x i, (q x i).length ≤ r.eval (List.length x) := by
  classical
  have h (i : Fin k) := output_length_poly (fun x => q x i) (hq i)
  choose p hp using h
  refine ⟨∑ i, p i, fun x i => ?_⟩
  refine (hp i x).trans ?_
  change _ ≤ (Polynomial.evalRingHom x.length) (∑ i, p i)
  rw [map_sum]
  exact Finset.single_le_sum (f := fun j => (Polynomial.evalRingHom x.length) (p j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem decideFixedTable {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (bp : ∀ x w : Word, v (x,w) = true → w.length = p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : (Fin k → Bool) → Bool)
    (relation : ∀ x : Word, x ∈ A ↔ T (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  classical
  obtain ⟨reduce, hr, hspec⟩ := hA _ (lexPrefixQuery_np hv p (fun x w h => (bp x w h).le))
  let q' := fun x i => q (reduce x) i
  have hq' (i : Fin k) : CPT (fun x => q' x i) := cpt_comp (g := fun x => q x i) hr (hq i)
  obtain ⟨r, rSize⟩ := tuple_length_bound k q' hq'
  obtain ⟨run, hrun, runSpec⟩ := compileTruthBoundary k q' hq'
  obtain ⟨m, hm⟩ := truthBoundaryBoundPolynomial k
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let count : Polynomial Nat := s.comp (r.comp width)
  let maxCount := m.comp count
  let prune := fun w : Word => run (unpairB w)
  have hprune : CPT prune := cpt_comp cpt_unpairB hrun
  apply decideOrderedSparse hv p bp count maxCount prune hprune
  intro n xs hn hxs
  have hw : width.eval n = 2*n + p.eval n + 1 := by simp [width]
  let S := acceptedShort B (r.eval (width.eval n))
  have hb : S.card ≤ count.eval n := by
    simpa [count, Polynomial.eval_comp] using sparse _ S (acceptedShort_spec B _)
  have htruth (y : Word) (hy : y ∈ xs) : y ∈ lexPrefixQuery v ↔ evalTT q' S T y = true := by
    have e : (fun i => decide (q' y i ∈ S)) =
        (fun i => @decide (q (reduce y) i ∈ B) (Classical.propDecidable _)) := by
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · exact fun h => (acceptedShort_spec B _ _ h).1
      · intro h
        have hl := (rSize y i).trans (eval_mono r ((hxs y hy).trans_eq hw.symm))
        exact mem_acceptedShort B _ _ h hl
    refine (hspec y).trans ((relation (reduce y)).trans ?_)
    rw [evalTT, e]
  let ys := keepTruthBoundary k (count.eval n) q' xs
  obtain ⟨hsub, hlen, hkeep⟩ := truthBoundarySpec k (count.eval n) q' xs hn
  have hOut : prune (pairB (un (count.eval n)) (encodeFrontier xs)) = encodeFrontier ys := by
    have h := runSpec (un (count.eval n)) xs
    simpa only [prune, unpairB_pairB, un_length, ys] using h
  refine ⟨ys,hOut,hsub,?_,fun left right x hx htrue hfalse => ?_⟩
  · simpa [maxCount, Polynomial.eval_comp, hm, ys] using hlen
  · apply hkeep S T x hb
    refine ⟨left,right,hx,?_,?_⟩
    · intro y hy
      have hy' : y ∈ xs := by
        rw [hx]
        simpa [List.append_assoc] using List.mem_append_left right hy
      exact (htruth y hy').mp (htrue y hy)
    · intro y hy
      have hy' : y ∈ xs := by rw [hx]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
      cases ht : evalTT q' S T y
      · rfl
      · exact False.elim (hfalse y hy ((htruth y hy').mpr ht))

/-- A fixed Boolean table of a fixed number of sparse membership queries for an NP-hard
language implies the pinned P = NP. All query coordinates are polynomial-time computable. -/
theorem FixedTruthTableSparseCollapse (A B : Language Bool) (hA : NPHard A)
    (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : (Fin k → Bool) → Bool)
    (relation : ∀ x : Word, x ∈ A ↔
      T (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro L hL
  obtain ⟨R,p,⟨v,spec,hv⟩,bound,he⟩ := ExactWitnessPadding L hL
  have hlen (x w : Word) (hw : v (x,w) = true) : w.length = p.eval x.length :=
    bound x w ((spec (x,w)).mpr hw)
  have e : L = ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) :=
    Set.ext (fun x => (he x).trans (exists_congr (fun w => spec (x,w))))
  rw [e]
  exact decideFixedTable hv p hlen A B hA s sparse k q hq T relation

end PEqualNP.Outside
