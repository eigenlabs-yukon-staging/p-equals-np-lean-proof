import PEqualNP.Outside.MeasuredBoundedTruthTableBoundary

namespace PEqualNP.Outside

local notation "Word" => List Bool
abbrev CandidateTable (k : Nat) := Word → (Fin k → Bool) → Bool

def mergeSelections (source left right : List Word) : List Word :=
  source.filter (fun x => x ∈ left ++ right)

theorem mergeSelections_mem (xs l r : List Word) (x : Word) :
    x ∈ mergeSelections xs l r ↔ x ∈ xs ∧ (x ∈ l ∨ x ∈ r) := by
  simp [mergeSelections, List.mem_filter]

theorem mergeSelections_sublist (xs l r : List Word) :
    (mergeSelections xs l r).Sublist xs := List.filter_sublist

theorem mergeSelections_length (xs l r : List Word) (hn : xs.Nodup) :
    (mergeSelections xs l r).length ≤ l.length + r.length := by
  have hd := hn.sublist (mergeSelections_sublist xs l r)
  have hsub : (mergeSelections xs l r).toFinset ⊆ (l ++ r).toFinset := by
    intro x hx
    simpa only [List.mem_toFinset, List.mem_append] using
      (mergeSelections_mem xs l r x).mp (List.mem_toFinset.mp hx) |>.2
  rw [← List.toFinset_card_of_nodup hd, ← List.length_append]
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le (l ++ r))

def defaultBucket {k : Nat} (t : CandidateTable k) (d : Bool) (xs : List Word) : List Word :=
  xs.filter (fun x => t x (fun _ => false) == d)

def trimByDefault {k : Nat} (t : CandidateTable k) (m : Nat) (xs : List Word) : List Word :=
  mergeSelections xs (trimBoundary m (defaultBucket t false xs))
    (trimBoundary m (defaultBucket t true xs))

theorem trimByDefault_sublist {k : Nat} (t : CandidateTable k) (m : Nat) (xs : List Word) :
    (trimByDefault t m xs).Sublist xs := mergeSelections_sublist _ _ _

theorem trimByDefault_length {k : Nat} (t : CandidateTable k) (m : Nat) (xs : List Word)
    (hn : xs.Nodup) : (trimByDefault t m xs).length ≤ 2 * (2*m+1) := by
  have h := mergeSelections_length xs
    (trimBoundary m (defaultBucket t false xs)) (trimBoundary m (defaultBucket t true xs)) hn
  have h0 := trimBoundary_length m (defaultBucket t false xs)
  have h1 := trimBoundary_length m (defaultBucket t true xs)
  unfold trimByDefault
  omega

private theorem trimByDefault_boundary {k : Nat} (q : Word → Fin k → Word) (t : CandidateTable k)
    (S : Finset Word) (m : Nat) (xs : List Word) (hn : xs.Nodup)
    (ht : (xs.filter (fun x => decide (∃ i, q x i ∈ S))).length ≤ m)
    (w : Word) (h : Boundary (fun x => evalTT q S (t x) x) xs w) :
    w ∈ trimByDefault t m xs := by
  let touch := fun x : Word => decide (∃ i, q x i ∈ S)
  let d := t w (fun _ => false)
  let group := defaultBucket t d xs
  have hsub : group.Sublist xs := List.filter_sublist
  have hw : w ∈ group := List.mem_filter.mpr ⟨h.mem, by simp [d]⟩
  have hcount : (group.filter touch).length ≤ m := ((hsub.filter touch).length_le).trans ht
  have hval (x : Word) (hx : x ∈ group) (hnone : touch x = false) :
      evalTT q S (t x) x = d := by
    have hxval : t x (fun _ => false) = d := by simpa using (List.mem_filter.mp hx).2
    unfold evalTT
    rw [← hxval]
    congr 1
    funext i
    by_cases hi : q x i ∈ S
    · have he : touch x = true := decide_eq_true ⟨i,hi⟩
      rw [hnone] at he
      contradiction
    · exact decide_eq_false hi
  have hkeep : w ∈ trimBoundary m group := by
    obtain ⟨l,r,eq,hl,hr⟩ := h.sublist hn hsub hw
    rw [eq] at hcount hval ⊢
    exact (TruthTableBoundaryTrim m l r w touch _ d hcount hval hl hr).2.2
  apply (mergeSelections_mem _ _ _ _).mpr
  refine ⟨h.mem, ?_⟩
  cases he : d
  · exact Or.inl (by simpa [group, he] using hkeep)
  · exact Or.inr (by simpa [group, he] using hkeep)

def compressedTTBound (b : Nat) : Nat → Nat
  | 0 => 2
  | k+1 => 2 * (2 * ((k+1) * b * (2 * compressedTTBound b k)) + 1)

def restrictTable {k : Nat} (t : CandidateTable (k+1)) (i : Fin (k+1)) (v : Bool) : CandidateTable k :=
  fun x a => t x (Fin.insertNth i v a)

def fiberSelect {k : Nat} (q : Word → Fin (k+1) → Word) (t : CandidateTable (k+1))
    (thin : (Word → Fin k → Word) → CandidateTable k → List Word → List Word)
    (i : Fin (k+1)) (xs : List Word) : List Word :=
  let q' := fun x j => q x (i.succAbove j)
  mergeSelections xs (thin q' (restrictTable t i false) xs) (thin q' (restrictTable t i true) xs)

def selectedFiberStep {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → List Word → List Word) (key : Fin k × Word) (xs : List Word) : List Word :=
  let chosen := thin key.1 (fiberList q key.1 key.2 xs)
  xs.filter (fun x => q x key.1 != key.2 || x ∈ chosen)

def foldSelectedFibers {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → List Word → List Word)
    (keys : List (Fin k × Word)) (xs : List Word) : List Word :=
  keys.foldl (fun ys key => selectedFiberStep q thin key ys) xs

theorem foldSelectedFibers_sublist {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → List Word → List Word) (keys : List (Fin k × Word)) (xs : List Word) :
    (foldSelectedFibers q thin keys xs).Sublist xs := by
  induction keys generalizing xs with
  | nil => exact List.Sublist.refl _
  | cons key keys ih => exact (ih _).trans List.filter_sublist

private theorem selectedFiberStep_cap {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → List Word → List Word) (key : Fin k × Word) (xs : List Word)
    (hn : xs.Nodup) (m : Nat)
    (small : ∀ i ys, ys.Nodup → (thin i ys).length ≤ m) :
    (fiberList q key.1 key.2 (selectedFiberStep q thin key xs)).length ≤ m := by
  let chosen := thin key.1 (fiberList q key.1 key.2 xs)
  let f := fiberList q key.1 key.2 (selectedFiberStep q thin key xs)
  have hnd : f.Nodup := hn.sublist (List.filter_sublist.trans List.filter_sublist)
  have hcards : f.toFinset ⊆ chosen.toFinset := by
    intro w hw
    have hf := List.mem_toFinset.mp hw
    have hkey : q w key.1 = key.2 := by simpa using (List.mem_filter.mp hf).2
    have hfilter := (List.mem_filter.mp (List.mem_filter.mp hf).1).2
    apply List.mem_toFinset.mpr
    simpa [hkey, chosen] using hfilter
  calc
    f.length = f.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ chosen.toFinset.card := Finset.card_le_card hcards
    _ ≤ chosen.length := List.toFinset_card_le _
    _ ≤ m := small _ _ (hn.sublist List.filter_sublist)

private theorem foldSelectedFibers_cap {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → List Word → List Word) (key : Fin k × Word) (keys : List (Fin k × Word))
    (hk : key ∈ keys) (xs : List Word) (hn : xs.Nodup) (m : Nat)
    (small : ∀ i ys, ys.Nodup → (thin i ys).length ≤ m) :
    (fiberList q key.1 key.2 (foldSelectedFibers q thin keys xs)).length ≤ m := by
  induction keys generalizing xs with
  | nil => simp at hk
  | cons next rest ih =>
    rcases List.mem_cons.mp hk with rfl | he
    · exact ((foldSelectedFibers_sublist q thin rest
        (selectedFiberStep q thin key xs)).filter _).length_le.trans
        (selectedFiberStep_cap q thin key xs hn m small)
    · exact ih he _ (hn.sublist List.filter_sublist)

private theorem foldSelectedFibers_boundary {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → List Word → List Word) (val : Word → Bool)
    (keys : List (Fin k × Word)) (xs : List Word) (hn : xs.Nodup) (w : Word)
    (keep : ∀ (key : Fin k × Word) (ys : List Word) (x : Word),
      ys.Nodup → (∀ y ∈ ys, q y key.1 = key.2) → Boundary val ys x → x ∈ thin key.1 ys)
    (h : Boundary val xs w) :
    Boundary val (foldSelectedFibers q thin keys xs) w := by
  induction keys generalizing xs with
  | nil => exact h
  | cons key rest ih =>
    let ys := selectedFiberStep q thin key xs
    have hsub : ys.Sublist xs := List.filter_sublist
    apply ih ys (hn.sublist hsub)
    apply h.sublist hn hsub
    apply List.mem_filter.mpr
    refine ⟨h.mem, ?_⟩
    by_cases he : q w key.1 = key.2
    · let frag := fiberList q key.1 key.2 xs
      have hw : w ∈ frag := List.mem_filter.mpr ⟨h.mem, by simpa using he⟩
      have hf : frag.Sublist xs := List.filter_sublist
      have hu := keep key frag w (hn.sublist hf)
        (fun y hy => by simpa using (List.mem_filter.mp hy).2)
        (h.sublist hn hf hw)
      simpa [he, frag] using hu
    · simp [he]

def keepCompressedBoundary : (k : Nat) → Nat → (Word → Fin k → Word) → CandidateTable k →
    List Word → List Word
  | 0, _, _, t, xs => trimByDefault t 0 xs
  | k+1, b, q, t, xs =>
    trimByDefault t ((k+1) * b * (2 * compressedTTBound b k))
      (foldSelectedFibers q (fiberSelect q t (keepCompressedBoundary k b)) (fiberKeys q xs) xs)

private theorem restrictTable_eval {k : Nat} (q : Word → Fin (k+1) → Word)
    (t : CandidateTable (k+1)) (S : Finset Word) (i : Fin (k+1)) (y x : Word)
    (h : q x i = y) :
    evalTT q S (t x) x =
      evalTT (fun w j => q w (i.succAbove j)) S
        (restrictTable t i (decide (y ∈ S)) x) x := by
  unfold evalTT restrictTable
  congr 1
  apply Fin.eq_insertNth_iff.mpr
  exact ⟨by rw [h], rfl⟩

theorem compressedBoundarySpec (k b : Nat) (q : Word → Fin k → Word)
    (t : CandidateTable k) (xs : List Word) (hn : xs.Nodup) :
    (keepCompressedBoundary k b q t xs).Sublist xs ∧
    (keepCompressedBoundary k b q t xs).length ≤ compressedTTBound b k ∧
    ∀ (S : Finset Word) (w : Word), S.card ≤ b →
      Boundary (fun x => evalTT q S (t x) x) xs w → w ∈ keepCompressedBoundary k b q t xs := by
  induction k generalizing xs with
  | zero =>
    refine ⟨trimByDefault_sublist _ _ _, trimByDefault_length _ _ _ hn, ?_⟩
    intro S w _ hw
    apply trimByDefault_boundary q t S 0 xs hn _ w hw
    simp
  | succ k ih =>
    let thin := fiberSelect q t (keepCompressedBoundary k b)
    let keys := fiberKeys q xs
    let reduced := foldSelectedFibers q thin keys xs
    let m := (k+1) * b * (2 * compressedTTBound b k)
    have hsub : reduced.Sublist xs := foldSelectedFibers_sublist _ _ _ _
    have hnd := hn.sublist hsub
    change (trimByDefault t m reduced).Sublist xs ∧
      (trimByDefault t m reduced).length ≤ _ ∧ _
    refine ⟨(trimByDefault_sublist _ _ _).trans hsub,
      trimByDefault_length _ _ _ hnd, ?_⟩
    intro S w hb hw
    have small (i : Fin (k+1)) (ys : List Word) (hy : ys.Nodup) :
        (thin i ys).length ≤ 2 * compressedTTBound b k := by
      have h0 := (ih (fun x j => q x (i.succAbove j)) (restrictTable t i false) ys hy).2.1
      have h1 := (ih (fun x j => q x (i.succAbove j)) (restrictTable t i true) ys hy).2.1
      have hm := mergeSelections_length ys
        (keepCompressedBoundary k b (fun x j => q x (i.succAbove j)) (restrictTable t i false) ys)
        (keepCompressedBoundary k b (fun x j => q x (i.succAbove j)) (restrictTable t i true) ys) hy
      exact hm.trans (by omega)
    have keep (key : Fin (k+1) × Word) (ys : List Word) (x : Word)
        (hy : ys.Nodup) (he : ∀ y ∈ ys, q y key.1 = key.2)
        (hx : Boundary (fun y => evalTT q S (t y) y) ys x) : x ∈ thin key.1 ys := by
      let q' := fun y j => q y (key.1.succAbove j)
      have hr := hx.congr (fun z hz => restrictTable_eval q t S key.1 key.2 z (he z hz))
      have hk := (ih q' (restrictTable t key.1 (decide (key.2 ∈ S))) ys hy).2.2 S x hb hr
      change x ∈ mergeSelections ys
        (keepCompressedBoundary k b q' (restrictTable t key.1 false) ys)
        (keepCompressedBoundary k b q' (restrictTable t key.1 true) ys)
      apply (mergeSelections_mem _ _ _ _).mpr
      refine ⟨hx.mem, ?_⟩
      cases h : decide (key.2 ∈ S) <;> rw [h] at hk
      · exact Or.inl hk
      · exact Or.inr hk
    have hkeep : Boundary (fun y => evalTT q S (t y) y) reduced w :=
      foldSelectedFibers_boundary q thin _ keys xs hn w keep hw
    have hcap (i : Fin (k+1)) (y : Word) :
        (reduced.toFinset.filter (fun x => q x i = y)).card ≤ 2 * compressedTTBound b k := by
      by_cases hk : (i,y) ∈ keys
      · have hc := foldSelectedFibers_cap q thin (i,y) keys hk xs hn _ small
        have he : (fiberList q i y reduced).toFinset = reduced.toFinset.filter (fun x => q x i = y) := by
          ext z
          simp [fiberList, List.mem_filter]
        rw [← he]
        exact (List.toFinset_card_le _).trans hc
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
      have hc := TruthTableTouchBound (k+1) reduced.toFinset S q
        (2 * compressedTTBound b k) (fun i y _ => hcap i y)
      have he : (reduced.filter touch).toFinset =
          reduced.toFinset.filter (fun x => ∃ i : Fin (k+1), q x i ∈ S) := by
        ext z
        simp [touch, List.mem_filter]
      rw [← he, List.toFinset_card_of_nodup (hnd.sublist List.filter_sublist)] at hc
      exact hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb))
    exact trimByDefault_boundary q t S m reduced hnd ht w hkeep

end PEqualNP.Outside
