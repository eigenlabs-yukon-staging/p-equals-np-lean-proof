import PEqualNP.Outside.MeasuredCompressedTruthBoundary
import PEqualNP.Outside.LastEncodedMatch
import PEqualNP.Outside.OrderedSparseFrontierSolver

namespace PEqualNP.Outside

open TruthTableSolver

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Verifier" => Word × Word → Bool

private theorem tuple_length_bound (k : Nat) (q : Word → Fin k → Word)
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

private def witnessPayload (s : Word) : Word :=
  sel s [] (true :: (unpairB s.tail).2)

private theorem witnessPayload_cpt : CPT witnessPayload :=
  cpt_sel cpt_id (cpt_const []) (cpt_cons1 true (cpt_unpairB2_1 cpt_tail))

private theorem last_at_minimum {xs : List Word} {c : Word} (hc : c ∈ xs)
    (horder : xs.Pairwise (fun a b => (unpairB b).2 < (unpairB a).2))
    (hmin : ∀ t ∈ xs, (unpairB c).2 ≤ (unpairB t).2) :
    xs.getLast? = some c := by
  obtain ⟨left,right,hs⟩ := List.append_of_mem hc
  have hnil : right = [] := by
    cases right with
    | nil => rfl
    | cons r rs =>
      have hm : r ∈ xs := by rw [hs]; simp
      have ho := (List.pairwise_append.mp (hs ▸ horder)).2.1
      have hlt : (unpairB r).2 < (unpairB c).2 :=
        (List.pairwise_cons.mp ho).1 r (by simp)
      exact False.elim ((not_lt_of_ge (hmin r hm)) hlt)
  rw [hs,hnil]
  simp

private theorem selectOrderedSparse {v : Word × Word → Bool}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (bound : ∀ x w : Word, v (x,w) = true → w.length = p.eval x.length)
    (count maxCount : Polynomial Nat) (prune : Word → Word) (hp : CPT prune)
    (hprune : OrderedPrunerSpec v p count maxCount prune) :
    ∃ f : Word → Word, CPT f ∧ ∀ x : Word,
      (f x = [] ∧ ∀ w : Word, v (x,w) = false) ∨
        ∃ w : Word, f x = true :: w ∧ v (x,w) = true ∧
          ∀ u : Word, v (x,u) = true → w ≤ u := by
  obtain ⟨out,hout,hs⟩ := runOrderedSparse p bound count maxCount prune hp hprune
  let pred := fun z : Word × Word => v (unpairB z.2)
  have hpred : ComputableInPolyTime encodePair Computability.encodeBool pred :=
    cpt_comp (cpt_comp cpt_snd cpt_unpairB) hv
  obtain ⟨last,hlast,lastSpec⟩ := LastEncodedMatch pred hpred
  let f := fun x : Word => witnessPayload (last ([],out x))
  have hf : CPT f :=
    cpt_comp (cpt_comp (cpt_pair (cpt_const []) hout) hlast) witnessPayload_cpt
  refine ⟨f,hf,fun x => ?_⟩
  obtain ⟨xs,hxs,horder,hshape,hmin⟩ := hs x
  let alive := xs.filter (fun y => v (unpairB y))
  have hspec : last ([],out x) = (alive.getLast?.map (List.cons true)).getD [] := by
    rw [hxs]
    exact lastSpec [] xs
  by_cases yes : ∃ w : Word, v (x,w) = true
  · obtain ⟨w,hw,hleast,hm⟩ := hmin yes
    have hc : pairB x w ∈ alive :=
      List.mem_filter.mpr ⟨hm, by simpa [unpairB_pairB] using hw⟩
    have hsort := horder.sublist (show alive.Sublist xs from List.filter_sublist)
    have hminimal (t : Word) (ht : t ∈ alive) : (unpairB (pairB x w)).2 ≤ (unpairB t).2 := by
      obtain ⟨htx,htv⟩ := List.mem_filter.mp ht
      obtain ⟨u,rfl,_⟩ := hshape t htx
      simpa only [unpairB_pairB] using hleast u (by simpa [unpairB_pairB] using htv)
    have he := last_at_minimum hc hsort hminimal
    exact Or.inr ⟨w,by simp [f,hspec,he,witnessPayload,sel,unpairB_pairB],hw,hleast⟩
  · have hn (w : Word) : v (x,w) = false := by
      cases h : v (x,w)
      · rfl
      · exact False.elim (yes ⟨w,h⟩)
    have he : alive = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro t ht
      obtain ⟨htx,htv⟩ := List.mem_filter.mp ht
      obtain ⟨u,rfl,_⟩ := hshape t htx
      simpa [unpairB_pairB,hn] using htv
    exact Or.inl ⟨by simp [f,hspec,he,witnessPayload],hn⟩

private theorem selectVariableTable {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (bp : ∀ x w : Word, v (x,w) = true → w.length = p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔ T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ∃ f : Word → Word, CPT f ∧ ∀ x : Word,
      (f x = [] ∧ ∀ w : Word, v (x,w) = false) ∨
        ∃ w : Word, f x = true :: w ∧ v (x,w) = true ∧
          ∀ u : Word, v (x,u) = true → w ≤ u := by
  classical
  obtain ⟨reduce, hr, hspec⟩ := hA _ (lexPrefixQuery_np hv p (fun x w h => (bp x w h).le))
  let q' := fun x i => q (reduce x) i
  have hq' (i : Fin k) : CPT (fun x => q' x i) := cpt_comp (g := fun x => q x i) hr (hq i)
  obtain ⟨r, rSize⟩ := tuple_length_bound k q' hq'
  let t' := fun x => T (reduce x)
  have ht' (a : Fin k → Bool) : ComputableInPolyTime (fun x : Word => x)
      Computability.encodeBool (fun x => t' x a) := cpt_comp (g := fun x => T x a) hr (hT a)
  obtain ⟨run, keep, hrun, runSpec, keepSpec⟩ := MeasuredCompressedTruthBoundary k q' t' hq' ht'
  obtain ⟨m,hm⟩ := compressedBoundPolynomial k
  have hrec (n j : Nat) : compressedTTBound n j =
      Nat.rec 1 (fun i a => 2 * ((i+1) * n * (2*a)) + 1) j := by
    induction j with
    | zero => rfl
    | succ j ih => simp [compressedTTBound,ih]
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let count : Polynomial Nat := s.comp (r.comp width)
  let maxCount := m.comp count
  let prune := fun w : Word => run (unpairB w)
  have hprune : CPT prune := cpt_comp cpt_unpairB hrun
  apply selectOrderedSparse hv p bp count maxCount prune hprune
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
  · simpa [maxCount, Polynomial.eval_comp, ys, hm, hrec] using hlen
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

/-- Under the sparse bounded truth-table hypothesis, the compressed frontier
machine returns the least exact-length witness, with an explicit failure tag. -/
theorem VariableTruthTableSparseWitness (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (exactLength : ∀ x w : Word, (x,w) ∈ R → w.length = p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔
      T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ∃ f : Word → Word, CPT f ∧ ∀ x : Word,
      (f x = [] ∧ ∀ w : Word, (x,w) ∉ R) ∨
        ∃ w : Word, f x = true :: w ∧ (x,w) ∈ R ∧
          ∀ u : Word, (x,u) ∈ R → w ≤ u := by
  obtain ⟨v,hvSpec,hv⟩ := hR
  have hlen (x w : Word) (h : v (x,w) = true) : w.length = p.eval x.length :=
    exactLength x w ((hvSpec (x,w)).mpr h)
  obtain ⟨f,hf,hs⟩ := selectVariableTable hv p hlen A B hA s sparse k q hq T hT relation
  refine ⟨f,hf,fun x => ?_⟩
  rcases hs x with ⟨hf',hn⟩ | ⟨w,hf',hw,hmin⟩
  · exact Or.inl ⟨hf',fun u hu => by have h := (hvSpec (x,u)).mp hu; simp [hn] at h⟩
  · exact Or.inr ⟨w,hf',(hvSpec (x,w)).mpr hw,
      fun u hu => hmin u ((hvSpec (x,u)).mp hu)⟩

end PEqualNP.Outside
