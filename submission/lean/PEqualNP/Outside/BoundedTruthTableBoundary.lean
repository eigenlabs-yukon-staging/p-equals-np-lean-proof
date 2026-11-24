import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Outside.TruthTableBoundaryTrim
import Mathlib.Data.Fin.Tuple.Basic

namespace PEqualNP.Outside

local notation "Word" => List Bool

/-- Bounded coordinate fibers restrict how many distinct candidate records can have
a query in the sparse set. Each such record lies in the union of the positive fibers. -/
theorem TruthTableTouchBound (k : Nat) (xs S : Finset (List Bool))
    (q : List Bool → Fin k → List Bool) (m : Nat)
    (fiber : ∀ i : Fin k, ∀ y ∈ S, (xs.filter (fun x => q x i = y)).card ≤ m) :
    (xs.filter (fun x => ∃ i : Fin k, q x i ∈ S)).card ≤ k * S.card * m := by
  let keys := (Finset.univ : Finset (Fin k)).product S
  let files := fun key : Fin k × List Bool => xs.filter (fun x => q x key.1 = key.2)
  have hi : xs.filter (fun x => ∃ i : Fin k, q x i ∈ S) ⊆ keys.biUnion files := by
    intro x hx
    obtain ⟨hx, i, hi⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_biUnion.mpr ⟨(i,q x i), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨hx, rfl⟩
  have hb : ∀ z ∈ keys, (files z).card ≤ m := by
    intro z hz
    exact fiber z.1 z.2 (Finset.mem_product.mp hz).2
  calc
    _ ≤ (keys.biUnion files).card := Finset.card_le_card hi
    _ ≤ ∑ z ∈ keys, (files z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ keys, m := Finset.sum_le_sum hb
    _ = k * S.card * m := by simp [keys]

private def Boundary (f : Word → Bool) (xs : List Word) (x : Word) : Prop :=
  ∃ left right : List Word, xs = left ++ x :: right ∧
    (∀ y ∈ left ++ [x], f y = true) ∧ (∀ y ∈ right, f y = false)

private theorem Boundary.mem {f : Word → Bool} {xs : List Word} {x : Word}
    (h : Boundary f xs x) : x ∈ xs := by
  obtain ⟨l,r,rfl,_,_⟩ := h
  simp

private theorem Boundary.sublist {f : Word → Bool} {xs ys : List Word} {x : Word}
    (h : Boundary f xs x) (hn : xs.Nodup) (hs : ys.Sublist xs) (hx : x ∈ ys) :
    Boundary f ys x := by
  obtain ⟨l,r,rfl,hgood,hbad⟩ := h
  have hnl : x ∉ l := by
    intro hl
    exact (List.nodup_append.mp hn).2.2 x hl x List.mem_cons_self rfl
  have hnr : x ∉ r := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  obtain ⟨l', r', rfl, hl', hr'⟩ := List.sublist_append_iff.mp hs
  have hxr : x ∈ r' := (List.mem_append.mp hx).resolve_left (fun hl => hnl (hl'.subset hl))
  rcases List.sublist_cons_iff.mp hr' with hs' | ⟨r'',rfl,hr''⟩
  · exact False.elim (hnr (hs'.subset hxr))
  · refine ⟨l',r'',rfl,?_,fun w hw => hbad w (hr''.subset hw)⟩
    intro y hy
    exact hgood y ((hl'.append_right [x]).subset hy)

private theorem Boundary.congr {f g : Word → Bool} {xs : List Word} {x : Word}
    (h : Boundary f xs x) (e : ∀ y ∈ xs, f y = g y) : Boundary g xs x := by
  obtain ⟨l,r,rfl,hgood,hbad⟩ := h
  refine ⟨l,r,rfl,?_,?_⟩
  · intro y hy
    have hm : y ∈ l ++ x :: r := by simpa [List.append_assoc] using List.mem_append_left r hy
    rw [← e y hm]
    exact hgood y hy
  · intro y hy
    rw [← e y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))]
    exact hbad y hy

private def evalTT {k : Nat} (q : Word → Fin k → Word) (S : Finset Word)
    (T : (Fin k → Bool) → Bool) (x : Word) : Bool :=
  T (fun i => decide (q x i ∈ S))

private def ttBound (b : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => 2 * ((k+1)*b*ttBound b k) + 1

private def fiberList {k : Nat} (q : Word → Fin k → Word) (i : Fin k) (y : Word)
    (xs : List Word) : List Word :=
  xs.filter (fun x => q x i == y)

private def fiberStep {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (key : Fin (k+1) × Word) (xs : List Word) : List Word :=
  let ys := fiberList q key.1 key.2 xs
  let kept := prune (fun w j => q w (key.1.succAbove j)) ys
  xs.filter (fun x => q x key.1 != key.2 || x ∈ kept)

private def fiberKeys {k : Nat} (q : Word → Fin k → Word) (xs : List Word) :
    List (Fin k × Word) :=
  (List.finRange k).flatMap (fun i => xs.map (fun x => (i, q x i)))

private def takeFibers {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (keys : List (Fin (k+1) × Word)) (xs : List Word) : List Word :=
  keys.foldl (fun ys key => fiberStep q prune key ys) xs

private def keepTruthBoundary : (k : Nat) → Nat → (Word → Fin k → Word) → List Word → List Word
  | 0, _, _, xs => trimBoundary 0 xs
  | k+1, b, q, xs =>
      trimBoundary ((k+1)*b*ttBound b k)
        (takeFibers q (keepTruthBoundary k b) (fiberKeys q xs) xs)

private theorem fiberStep_sublist {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (key : Fin (k+1) × Word) (xs : List Word) :
    (fiberStep q prune key xs).Sublist xs :=
  List.filter_sublist

private theorem fiberStep_cap {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (key : Fin (k+1) × Word) (xs : List Word) (m : Nat) (hn : xs.Nodup)
    (hprune : ∀ query : Word → Fin k → Word, ∀ ys : List Word, ys.Nodup →
      (prune query ys).length ≤ m) :
    (fiberList q key.1 key.2 (fiberStep q prune key xs)).length ≤ m := by
  let kept := prune (fun w j => q w (key.1.succAbove j)) (fiberList q key.1 key.2 xs)
  have hb : kept.length ≤ m := hprune _ _ (List.Nodup.sublist List.filter_sublist hn)
  let f := fiberList q key.1 key.2 (fiberStep q prune key xs)
  have hf : f.Nodup := List.Nodup.sublist
    (show f.Sublist xs from List.filter_sublist.trans (fiberStep_sublist q prune key xs)) hn
  have hs : f.toFinset ⊆ kept.toFinset := by
    intro w hw
    have hw' := List.mem_toFinset.mp hw
    have he : q w key.1 = key.2 := by simpa using (List.mem_filter.mp hw').2
    have hd := (List.mem_filter.mp (List.mem_filter.mp hw').1).2
    apply List.mem_toFinset.mpr
    simpa [kept, he] using hd
  have hkeep : kept.toFinset.card ≤ kept.length := List.toFinset_card_le kept
  exact (List.toFinset_card_of_nodup hf).symm.le.trans
    ((Finset.card_le_card hs).trans (hkeep.trans hb))

private theorem takeFibers_sublist {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (keys : List (Fin (k+1) × Word)) (xs : List Word) :
    (takeFibers q prune keys xs).Sublist xs := by
  induction keys generalizing xs with
  | nil => exact List.Sublist.refl _
  | cons key keys ih =>
    exact (ih (fiberStep q prune key xs)).trans (fiberStep_sublist q prune key xs)

private theorem takeFibers_cap {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (key : Fin (k+1) × Word) (keys : List (Fin (k+1) × Word))
    (hk : key ∈ keys) (xs : List Word) (hn : xs.Nodup) (m : Nat)
    (hprune : ∀ query : Word → Fin k → Word, ∀ ys : List Word, ys.Nodup →
      (prune query ys).length ≤ m) :
    (fiberList q key.1 key.2 (takeFibers q prune keys xs)).length ≤ m := by
  induction keys generalizing xs with
  | nil => simp at hk
  | cons next rest ih =>
    let ys := fiberStep q prune next xs
    have hys := List.Nodup.sublist (fiberStep_sublist q prune next xs) hn
    rcases List.mem_cons.mp hk with rfl | he
    · have h0 := fiberStep_cap q prune key xs m hn hprune
      have h1 := (takeFibers_sublist q prune rest (fiberStep q prune key xs)).filter
        (fun x => q x key.1 == key.2)
      exact h1.length_le.trans h0
    · exact ih he ys hys

private theorem restrictEval {k : Nat} (q : Word → Fin (k+1) → Word)
    (S : Finset Word) (T : (Fin (k+1) → Bool) → Bool) (i : Fin (k+1)) (y x : Word)
    (h : q x i = y) :
    evalTT q S T x =
      evalTT (fun w j => q w (i.succAbove j)) S
        (fun bs => T (Fin.insertNth i (decide (y ∈ S)) bs)) x := by
  unfold evalTT
  congr 1
  apply Fin.eq_insertNth_iff.mpr
  exact ⟨by rw [h], rfl⟩

private theorem fiberStep_boundary {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (key : Fin (k+1) × Word) (xs : List Word) (hn : xs.Nodup) (b : Nat)
    (hprune : ∀ (g : Word → Fin k → Word) (ys : List Word), ys.Nodup →
      ∀ (S : Finset Word) (T : (Fin k → Bool) → Bool) (w : Word),
        S.card ≤ b → Boundary (evalTT g S T) ys w → w ∈ prune g ys)
    (S : Finset Word) (T : (Fin (k+1) → Bool) → Bool) (w : Word)
    (hS : S.card ≤ b) (h : Boundary (evalTT q S T) xs w) :
    Boundary (evalTT q S T) (fiberStep q prune key xs) w := by
  apply h.sublist hn (fiberStep_sublist q prune key xs)
  apply List.mem_filter.mpr
  refine ⟨h.mem, ?_⟩
  by_cases he : q w key.1 = key.2
  · let frag := fiberList q key.1 key.2 xs
    have hw : w ∈ frag := List.mem_filter.mpr ⟨h.mem, by simpa using he⟩
    have hsub : frag.Sublist xs := List.filter_sublist
    have hh := h.sublist hn hsub hw
    have hh' := hh.congr (fun x hx => restrictEval q S T key.1 key.2 x
      (by simpa using (List.mem_filter.mp hx).2))
    have hk := hprune _ frag (List.Nodup.sublist hsub hn) S _ w hS hh'
    simpa [he] using hk
  · simp [he]

private theorem takeFibers_boundary {k : Nat} (q : Word → Fin (k+1) → Word)
    (prune : (Word → Fin k → Word) → List Word → List Word)
    (keys : List (Fin (k+1) × Word)) (xs : List Word) (hn : xs.Nodup) (b : Nat)
    (hprune : ∀ (g : Word → Fin k → Word) (ys : List Word), ys.Nodup →
      ∀ (S : Finset Word) (T : (Fin k → Bool) → Bool) (w : Word),
        S.card ≤ b → Boundary (evalTT g S T) ys w → w ∈ prune g ys)
    (S : Finset Word) (T : (Fin (k+1) → Bool) → Bool) (w : Word)
    (hS : S.card ≤ b) (h : Boundary (evalTT q S T) xs w) :
    Boundary (evalTT q S T) (takeFibers q prune keys xs) w := by
  induction keys generalizing xs with
  | nil => exact h
  | cons key rest ih =>
    have hsub := fiberStep_sublist q prune key xs
    have hb := fiberStep_boundary q prune key xs hn b hprune S T w hS h
    exact ih _ (List.Nodup.sublist hsub hn) hb

private theorem touch_default {k : Nat} (q : Word → Fin k → Word) (S : Finset Word)
    (T : (Fin k → Bool) → Bool) (x : Word)
    (hx : decide (∃ i : Fin k, q x i ∈ S) = false) :
    evalTT q S T x = T (fun _ => false) := by
  unfold evalTT
  congr 1
  funext i
  apply decide_eq_false
  intro hi
  have h := decide_eq_true (show ∃ i : Fin k, q x i ∈ S from ⟨i,hi⟩)
  rw [h] at hx
  contradiction

private theorem truthBoundarySpec (k b : Nat) (q : Word → Fin k → Word) (xs : List Word)
    (hn : xs.Nodup) :
    (keepTruthBoundary k b q xs).Sublist xs ∧
    (keepTruthBoundary k b q xs).length ≤ ttBound b k ∧
    ∀ (S : Finset Word) (T : (Fin k → Bool) → Bool) (w : Word),
      S.card ≤ b → Boundary (evalTT q S T) xs w → w ∈ keepTruthBoundary k b q xs := by
  induction k generalizing xs with
  | zero =>
    refine ⟨trimBoundary_sublist _ _, trimBoundary_length _ _, ?_⟩
    intro S T w _ h
    obtain ⟨left,right,rfl,hgood,hbad⟩ := h
    exact (TruthTableBoundaryTrim 0 left right w (fun _ => false) (evalTT q S T) (T (fun _ => false))
      (by simp) (fun x _ _ => touch_default q S T x (by simp)) hgood hbad).2.2
  | succ k ih =>
    let reduced := takeFibers q (keepTruthBoundary k b) (fiberKeys q xs) xs
    let m := (k+1)*b*ttBound b k
    have hsub : reduced.Sublist xs := takeFibers_sublist _ _ _ _
    have hnd : reduced.Nodup := List.Nodup.sublist hsub hn
    have hkeep (g : Word → Fin k → Word) (ys : List Word) (hy : ys.Nodup) :=
      (ih g ys hy).2.2
    refine ⟨(trimBoundary_sublist m reduced).trans hsub, trimBoundary_length m reduced, ?_⟩
    intro S T w hb hs
    have hboundary : Boundary (evalTT q S T) reduced w :=
      takeFibers_boundary q _ _ xs hn b hkeep S T w hb hs
    have hcap (i : Fin (k+1)) (y : Word) : (reduced.toFinset.filter (fun x => q x i = y)).card ≤ ttBound b k := by
      by_cases hk : (i,y) ∈ fiberKeys q xs
      · have hc := takeFibers_cap q (keepTruthBoundary k b) (i,y) _ hk xs hn _
          (fun g ys h => (ih g ys h).2.1)
        have h := List.toFinset_card_le (l := fiberList q i y reduced)
        have he : (fiberList q i y reduced).toFinset = reduced.toFinset.filter (fun x => q x i = y) := by
          ext z
          simp [fiberList, List.mem_filter]
        rw [← he]
        exact h.trans hc
      · have he : reduced.toFinset.filter (fun x => q x i = y) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hz
          obtain ⟨hzm,hze⟩ := Finset.mem_filter.mp hz
          have hzxs := hsub.subset (List.mem_toFinset.mp hzm)
          apply hk
          refine List.mem_flatMap.mpr ⟨i, by simp, ?_⟩
          exact List.mem_map.mpr ⟨z, hzxs, by simp [hze]⟩
        simp [he]
    let touch := fun x : Word => decide (∃ i : Fin (k+1), q x i ∈ S)
    have ht : (reduced.filter touch).length ≤ m := by
      have hc := TruthTableTouchBound (k+1) reduced.toFinset S q (ttBound b k) (fun i y _ => hcap i y)
      have he : (reduced.filter touch).toFinset =
          reduced.toFinset.filter (fun x => ∃ i : Fin (k+1), q x i ∈ S) := by
        ext z
        simp [touch, List.mem_filter]
      rw [← he, List.toFinset_card_of_nodup (List.Nodup.sublist List.filter_sublist hnd)] at hc
      exact hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb))
    obtain ⟨left,right,eq,hgood,hbad⟩ := hboundary
    change w ∈ trimBoundary m reduced
    rw [eq] at ht ⊢
    exact (TruthTableBoundaryTrim m left right w touch (evalTT q S T) (T (fun _ => false))
      ht (fun x _ hx => touch_default q S T x hx) hgood hbad).2.2

/-- Uniform bounded truth-table frontier pruning at the list level. The output
depends on the query tuples and bound only. Its correctness covers every Boolean
table and sparse target that make the input a true prefix followed by a false suffix. -/
theorem BoundedTruthTableBoundary (k : Nat) (q : Word → Fin k → Word) :
    ∃ prune : Nat → List Word → List Word,
      ∀ (b : Nat) (xs : List Word), xs.Nodup →
        let limit := Nat.rec 1 (fun j acc => 2*((j+1)*b*acc)+1) k
        (prune b xs).Sublist xs ∧ (prune b xs).length ≤ limit ∧
        ∀ (S : Finset Word) (T : (Fin k → Bool) → Bool) (left right : List Word) (x : Word),
          S.card ≤ b → xs = left ++ x :: right →
          (∀ y ∈ left ++ [x], T (fun i => decide (q y i ∈ S)) = true) →
          (∀ y ∈ right, T (fun i => decide (q y i ∈ S)) = false) →
          x ∈ prune b xs := by
  refine ⟨fun b => keepTruthBoundary k b q, fun b xs hn => ?_⟩
  have hlim (j : Nat) : ttBound b j = Nat.rec 1 (fun i acc => 2*((i+1)*b*acc)+1) j := by
    induction j with
    | zero => rfl
    | succ j ih => simp [ttBound, ih]
  obtain ⟨hsub, hsize, hbound⟩ := truthBoundarySpec k b q xs hn
  refine ⟨hsub, hsize.trans_eq (hlim k), fun S T left right x hb he hgood hbad => ?_⟩
  exact hbound S T x hb ⟨left,right,he,hgood,hbad⟩

end PEqualNP.Outside
