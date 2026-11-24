import PEqualNP.Defs

namespace PEqualNP.Outside

local notation "Word" => List Bool

def trimBoundary (m : Nat) (xs : List Word) : List Word :=
  xs.take m ++ xs.drop (max m (xs.length - (m+1)))

theorem trimBoundary_sublist (m : Nat) (xs : List Word) : (trimBoundary m xs).Sublist xs := by
  unfold trimBoundary
  have h := List.drop_sublist_drop_left xs (le_max_left m (xs.length - (m+1)))
  simpa using h.append_left (xs.take m)

theorem trimBoundary_length (m : Nat) (xs : List Word) :
    (trimBoundary m xs).length ≤ 2*m + 1 := by
  simp only [trimBoundary, List.length_append, List.length_take, List.length_drop]
  omega

private theorem take_has_left (m : Nat) (left right : List Word) (x : Word)
    (h : left.length < m) : x ∈ (left ++ x :: right).take m := by
  induction left generalizing m with
  | nil =>
    cases m with
    | zero => simp at h
    | succ m => simp
  | cons y ys ih =>
    cases m with
    | zero => simp at h
    | succ m =>
      simp only [List.cons_append, List.take_succ_cons]
      exact List.mem_cons_of_mem _ (ih m (by simp only [List.length_cons] at h; omega))

private theorem drop_has_cut (m : Nat) (left right : List Word) (x : Word)
    (h : m ≤ left.length) : x ∈ (left ++ x :: right).drop m := by
  induction left generalizing m with
  | nil =>
    have e : m = 0 := by simpa using h
    simp [e]
  | cons y ys ih =>
    cases m with
    | zero => simp
    | succ m =>
      simp only [List.cons_append, List.drop_succ_cons]
      exact ih m (by simpa using h)

/-- If all but at most m positions have the same hidden Boolean value, retaining the
first m and last m+1 positions preserves the end of every true-then-false boundary. -/
theorem TruthTableBoundaryTrim (m : Nat) (left right : List Word) (x : Word)
    (touch value : Word → Bool) (default : Bool)
    (hcount : ((left ++ x :: right).filter touch).length ≤ m)
    (stable : ∀ y ∈ left ++ x :: right, touch y = false → value y = default)
    (positive : ∀ y ∈ left ++ [x], value y = true)
    (negative : ∀ y ∈ right, value y = false) :
    let xs := left ++ x :: right
    let ys := xs.take m ++ xs.drop (max m (xs.length - (m+1)))
    ys.Sublist xs ∧ ys.length ≤ 2*m + 1 ∧ x ∈ ys := by
  change (trimBoundary m (left ++ x :: right)).Sublist (left ++ x :: right) ∧
    (trimBoundary m (left ++ x :: right)).length ≤ 2*m + 1 ∧ x ∈ trimBoundary m (left ++ x :: right)
  refine ⟨trimBoundary_sublist _ _, trimBoundary_length _ _, ?_⟩
  have memPos (y : Word) (hy : y ∈ left ++ [x]) : y ∈ left ++ x :: right := by
    simpa [List.append_assoc] using List.mem_append_left right hy
  have memNeg (y : Word) (hy : y ∈ right) : y ∈ left ++ x :: right :=
    List.mem_append_right _ (List.mem_cons_of_mem _ hy)
  cases default with
  | false =>
    have hfilter : (left ++ [x]).filter touch = left ++ [x] := by
      apply List.filter_eq_self.mpr
      intro y hy
      cases ht : touch y
      · have hv := (positive y hy).symm.trans (stable y (memPos y hy) ht)
        contradiction
      · rfl
    have h : ((left ++ x :: right).filter touch).length =
        left.length + 1 + (right.filter touch).length := by
      have he : left ++ x :: right = (left ++ [x]) ++ right := by simp [List.append_assoc]
      rw [he, List.filter_append, hfilter]
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    unfold trimBoundary
    exact List.mem_append_left _ (take_has_left m left right x (by omega))
  | true =>
    have hfilter : right.filter touch = right := by
      apply List.filter_eq_self.mpr
      intro y hy
      cases ht : touch y
      · have hv := (negative y hy).symm.trans (stable y (memNeg y hy) ht)
        contradiction
      · rfl
    have h : right.length ≤ m := by
      simp only [List.filter_append, List.filter_cons, hfilter, List.length_append] at hcount
      cases ht : touch x <;> simp [ht] at hcount <;> omega
    unfold trimBoundary
    by_cases hl : left.length < m
    · exact List.mem_append_left _ (take_has_left m left right x hl)
    · apply List.mem_append_right
      apply drop_has_cut
      simp
      omega

end PEqualNP.Outside
