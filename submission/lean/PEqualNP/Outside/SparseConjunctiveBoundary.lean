import PEqualNP.Defs
import Mathlib.Data.List.Dedup

namespace PEqualNP.Outside

local notation "Word" => List Bool

def rightPrune (q : Word → List Word) :
    (xs : List Word) → Nat → List Word → Option Word → List Word
  | _, 0, _, _ => []
  | [], _+1, _, prev => prev.toList
  | x :: xs, fuel+1, seen, prev =>
    if ∃ y ∈ q x, y ∉ seen then
      prev.toList ++ rightPrune q xs fuel (seen ++ q x) (some x)
    else rightPrune q xs (fuel+1) seen (some x)

private theorem rightPrune_sublist (q : Word → List Word) (xs : List Word)
    (fuel : Nat) (seen : List Word) (prev : Option Word) :
    (rightPrune q xs fuel seen prev).Sublist (prev.toList ++ xs) := by
  induction xs generalizing fuel seen prev with
  | nil =>
    cases fuel <;> simp [rightPrune]
  | cons x xs ih =>
    cases fuel with
    | zero => simp [rightPrune]
    | succ fuel =>
      by_cases h : ∃ y ∈ q x, y ∉ seen
      · have hi := ih fuel (seen ++ q x) (some x)
        simp only [Option.toList_some, List.singleton_append] at hi
        simpa [rightPrune, h] using hi.append_left prev.toList
      · have hi := ih (fuel+1) seen (some x)
        simp only [Option.toList_some, List.singleton_append] at hi
        simpa [rightPrune, h] using hi.trans (List.sublist_append_right prev.toList _)

private theorem rightPrune_length (q : Word → List Word) (xs : List Word) (fuel : Nat)
    (seen : List Word) (prev : Option Word) :
    (rightPrune q xs fuel seen prev).length ≤ fuel + 1 := by
  induction xs generalizing fuel seen prev with
  | nil => cases fuel <;> cases prev <;> simp [rightPrune]
  | cons x xs ih =>
    cases fuel with
    | zero => simp [rightPrune]
    | succ fuel =>
      by_cases h : ∃ y ∈ q x, y ∉ seen
      · have hi := ih fuel (seen ++ q x) (some x)
        have hl : prev.toList.length ≤ 1 := by cases prev <;> simp
        simp only [rightPrune, h, ite_true, List.length_append]
        omega
      · simpa [rightPrune, h] using ih (fuel+1) seen (some x)

private theorem seen_card_grows (seen qs : List Word) (h : ∃ w ∈ qs, w ∉ seen) :
    seen.toFinset.card < (seen ++ qs).toFinset.card := by
  obtain ⟨w, hw, hno⟩ := h
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro u hu
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hu))
  · intro eq
    apply hno
    apply List.mem_toFinset.mp
    rw [eq]
    exact List.mem_toFinset.mpr (List.mem_append_right _ hw)

private def latest : Option Word → List Word → Option Word
  | p, [] => p
  | _, x :: xs => latest (some x) xs

private theorem latest_snoc (xs : List Word) (p : Option Word) (x : Word) :
    latest p (xs ++ [x]) = some x := by
  induction xs generalizing p with
  | nil => rfl
  | cons y ys ih => exact ih (some y)

private theorem rightPrune_boundary (q : Word → List Word) (S : Finset Word)
    (good rest : List Word) (seen : List Word) (prev : Option Word) (fuel : Nat)
    (hseen : ∀ w ∈ seen, w ∈ S)
    (hbudget : S.card < seen.toFinset.card + fuel)
    (hgood : ∀ x ∈ good, ∀ w ∈ q x, w ∈ S)
    (hrest : rest = [] ∨ ∃ x xs, rest = x::xs ∧ ∃ w ∈ q x, w ∉ S) :
    (latest prev good).toList.Sublist (rightPrune q (good ++ rest) fuel seen prev) := by
  induction good generalizing seen prev fuel with
  | nil =>
    have hcard : seen.toFinset.card ≤ S.card := Finset.card_le_card (by
      intro w hw
      exact hseen w (List.mem_toFinset.mp hw))
    have hfuel : 0 < fuel := by omega
    cases fuel with
    | zero => omega
    | succ fuel =>
      rcases hrest with e | ⟨x,xs,e,w,hw,hno⟩
      · subst rest
        simp [rightPrune, latest]
      · subst rest
        have hnew : ∃ w ∈ q x, w ∉ seen := ⟨w, hw, fun h => hno (hseen w h)⟩
        simpa [latest, rightPrune, hnew] using
          (List.sublist_append_left prev.toList (rightPrune q xs fuel (seen ++ q x) (some x)))
  | cons x xs ih =>
    have hcard : seen.toFinset.card ≤ S.card := Finset.card_le_card (by
      intro w hw
      exact hseen w (List.mem_toFinset.mp hw))
    have hfuel : 0 < fuel := by omega
    have ht : ∀ y ∈ xs, ∀ w ∈ q y, w ∈ S :=
      fun y hy => hgood y (List.mem_cons_of_mem _ hy)
    cases fuel with
    | zero => omega
    | succ fuel =>
      by_cases hnew : ∃ w ∈ q x, w ∉ seen
      · have hseen' (w : Word) (hw : w ∈ seen ++ q x) : w ∈ S :=
          (List.mem_append.mp hw).elim (hseen w) (hgood x List.mem_cons_self w)
        have hstrict := seen_card_grows seen (q x) hnew
        have hi := ih (seen ++ q x) (some x) fuel hseen' (by omega) ht
        simp only [latest, List.cons_append, rightPrune, hnew, ite_true]
        exact hi.trans (List.sublist_append_right _ _)
      · simpa [latest, rightPrune, hnew] using ih seen (some x) (fuel+1) hseen hbudget ht

theorem rightPrune_public (q : Word → List Word) :
    (∀ b xs, (rightPrune q xs (b+1) [] none).Sublist xs ∧
      (rightPrune q xs (b+1) [] none).length ≤ b + 2) ∧
    ∀ (b : Nat) (S : Finset Word), S.card ≤ b →
      ∀ (good rest : List Word) (x : Word),
        (∀ y ∈ good ++ [x], ∀ w ∈ q y, w ∈ S) →
        (rest = [] ∨ ∃ y ys, rest = y :: ys ∧ ∃ w ∈ q y, w ∉ S) →
        x ∈ rightPrune q ((good ++ [x]) ++ rest) (b+1) [] none := by
  constructor
  · intro b xs
    exact ⟨rightPrune_sublist q xs _ [] none, rightPrune_length q xs _ [] none⟩
  · intro b S hb good rest x hgood hrest
    have hr := rightPrune_boundary q S (good ++ [x]) rest [] none (b+1)
      (by simp) (by simp; omega) hgood hrest
    rw [latest_snoc] at hr
    exact hr.subset (by simp)

/-- The same computation preserves the last true point of any ordered conjunctive
prefix before its first false point, uniformly over the hidden sparse set. -/
theorem SparseConjunctiveBoundary (q : Word → List Word) :
    ∃ prune : Nat → List Word → List Word,
      (∀ b xs, (prune b xs).Sublist xs ∧ (prune b xs).length ≤ b + 2) ∧
      ∀ (b : Nat) (S : Finset Word), S.card ≤ b →
        ∀ (good rest : List Word) (x : Word),
          (∀ y ∈ good ++ [x], ∀ w ∈ q y, w ∈ S) →
          (rest = [] ∨ ∃ y ys, rest = y :: ys ∧ ∃ w ∈ q y, w ∉ S) →
          x ∈ prune b ((good ++ [x]) ++ rest) := by
  exact ⟨fun b xs => rightPrune q xs (b+1) [] none, rightPrune_public q⟩

end PEqualNP.Outside
