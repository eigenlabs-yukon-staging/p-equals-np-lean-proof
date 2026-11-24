import PEqualNP.Outside.VariableTruthTableBoundary
import PEqualNP.Outside.FixedTruthTableSparseCollapse

namespace PEqualNP.Outside

open TruthTableSolver

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Verifier" => Word × Word → Bool

private theorem decideVariableTable {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (bp : ∀ x w : Word, v (x,w) = true → w.length = p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔ T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  classical
  obtain ⟨reduce, hr, hspec⟩ := hA _ (lexPrefixQuery_np hv p (fun x w h => (bp x w h).le))
  let q' := fun x i => q (reduce x) i
  have hq' (i : Fin k) : CPT (fun x => q' x i) := cpt_comp (g := fun x => q x i) hr (hq i)
  obtain ⟨r, rSize⟩ := tuple_length_bound k q' hq'
  let t' := fun x => T (reduce x)
  have ht' (a : Fin k → Bool) : ComputableInPolyTime (fun x : Word => x)
      Computability.encodeBool (fun x => t' x a) := cpt_comp (g := fun x => T x a) hr (hT a)
  obtain ⟨run, keep, m, hrun, runSpec, keepSpec⟩ := VariableTruthTableBoundary k q' t' hq' ht' 
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
  have htruth (y : Word) (hy : y ∈ xs) : y ∈ lexPrefixQuery v ↔ t' y (fun i => decide (q' y i ∈ S)) = true := by
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
    rw [e] <;> rfl
  let ys := keep (count.eval n) xs
  obtain ⟨hsub, hlen, hkeep⟩ := keepSpec (count.eval n) xs hn
  have hOut : prune (pairB (un (count.eval n)) (encodeFrontier xs)) = encodeFrontier ys := by
    have h := runSpec (un (count.eval n)) xs
    change run (un (count.eval n), encodeFrontier xs) =
      encodeFrontier (keep (un (count.eval n)).length xs) at h
    simpa only [prune, unpairB_pairB, un_length, ys] using h
  refine ⟨ys,hOut,hsub,?_,fun left right x hx htrue hfalse => ?_⟩
  · simpa [maxCount, Polynomial.eval_comp, ys] using hlen
  · refine hkeep S left right x hb hx ?_ ?_
    · intro y hy
      have hy' : y ∈ xs := by
        rw [hx]
        simpa [List.append_assoc] using List.mem_append_left right hy
      exact (htruth y hy').mp (htrue y hy)
    · intro y hy
      have hy' : y ∈ xs := by rw [hx]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
      cases ht : t' y (fun i => decide (q' y i ∈ S))
      · rfl
      · exact False.elim (hfalse y hy ((htruth y hy').mpr ht))

/-- A bounded truth-table reduction of a pinned NP-hard language to a sparse target
implies P = NP. The fixed collection of query coordinates and table entries are measured. -/
theorem VariableTruthTableSparseCollapse (A B : Language Bool) (hA : NPHard A)
    (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔
      T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro L hL
  obtain ⟨R,p,⟨v,spec,hv⟩,bound,he⟩ := ExactWitnessPadding L hL
  have hlen (x w : Word) (hw : v (x,w) = true) : w.length = p.eval x.length :=
    bound x w ((spec (x,w)).mpr hw)
  have e : L = ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) :=
    Set.ext (fun x => (he x).trans (exists_congr (fun w => spec (x,w))))
  rw [e]
  exact decideVariableTable hv p hlen A B hA s sparse k q hq T hT relation

end PEqualNP.Outside
