import PEqualNP.Defs

namespace PEqualNP.Outside

local notation "Word" => List Bool

def trimDirected (default : Bool) (m : Nat) (xs : List Word) : List Word :=
  if default then xs.drop (xs.length - (m+1)) else xs.take m

theorem trimDirected_sublist (default : Bool) (m : Nat) (xs : List Word) :
    (trimDirected default m xs).Sublist xs := by
  cases default
  · exact List.take_sublist _ _
  · exact List.drop_sublist _ _

theorem trimDirected_length (default : Bool) (m : Nat) (xs : List Word) :
    (trimDirected default m xs).length ≤ m + default.toNat := by
  cases default
  · simp [trimDirected]
  · simp [trimDirected, Bool.toNat]
    omega

private theorem cutoff_in_take (m : Nat) (l r : List Word) (w : Word) (h : l.length < m) :
    w ∈ (l ++ w::r).take m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | zero => simp at h
    | succ m => simp
  | cons x l ih =>
    cases m with
    | zero => simp at h
    | succ m =>
      simp only [List.cons_append, List.take_succ_cons]
      exact List.mem_cons_of_mem _ (ih m (by simpa using h))

private theorem cutoff_in_drop (n : Nat) (l r : List Word) (w : Word) (h : n ≤ l.length) :
    w ∈ (l ++ w::r).drop n := by
  induction l generalizing n with
  | nil =>
    have eq : n = 0 := by simpa using h
    simp [eq]
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.cons_append, List.drop_succ_cons]
      exact ih n (by simpa using h)

/-- A known default false value requires only the front portion of the list,
while a known default true value requires only the back portion. -/
theorem DirectionalTruthTableTrim (m : Nat) (l r : List Word) (w : Word)
    (touch value : Word → Bool) (default : Bool)
    (hcount : ((l ++ w::r).filter touch).length ≤ m)
    (stable : ∀ y ∈ l ++ w::r, touch y = false → value y = default)
    (pos : ∀ y ∈ l ++ [w], value y = true)
    (neg : ∀ y ∈ r, value y = false) :
    let xs := l ++ w::r
    let ys := if default then xs.drop (xs.length - (m+1)) else xs.take m
    ys.Sublist xs ∧ ys.length ≤ m + default.toNat ∧ w ∈ ys := by
  change (trimDirected default m (l ++ w::r)).Sublist (l ++ w::r) ∧
    (trimDirected default m (l ++ w::r)).length ≤ m + default.toNat ∧
    w ∈ trimDirected default m (l ++ w::r)
  refine ⟨trimDirected_sublist _ _ _, trimDirected_length _ _ _, ?_⟩
  cases default with
  | false =>
    have hall : (l ++ [w]).filter touch = l ++ [w] := by
      apply List.filter_eq_self.mpr
      intro y hy
      have hm : y ∈ l ++ w::r := by
        simpa only [List.append_assoc, List.singleton_append] using List.mem_append_left r hy
      cases he : touch y with
      | false => exact False.elim (Bool.noConfusion ((pos y hy).symm.trans (stable y hm he)))
      | true => rfl
    have he : l ++ w::r = (l ++ [w]) ++ r := by simp [List.append_assoc]
    rw [he, List.filter_append, hall] at hcount
    simp only [List.length_append, List.length_singleton] at hcount
    exact cutoff_in_take m l r w (by omega)
  | true =>
    have hall : r.filter touch = r := by
      apply List.filter_eq_self.mpr
      intro y hy
      have hm := List.mem_append_right l (List.mem_cons_of_mem w hy)
      cases he : touch y with
      | false => exact False.elim (Bool.noConfusion ((neg y hy).symm.trans (stable y hm he)))
      | true => rfl
    simp only [List.filter_append, List.filter_cons, hall, List.length_append] at hcount
    have hr : r.length ≤ m := by split at hcount <;> (try simp only [List.length_cons] at hcount) <;> omega
    apply cutoff_in_drop
    simp only [List.length_append, List.length_cons]
    omega

end PEqualNP.Outside
