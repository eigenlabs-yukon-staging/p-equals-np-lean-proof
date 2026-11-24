import PEqualNP.Defs
import Mathlib.Data.List.Dedup

namespace PEqualNP.Outside

def sparseListRepresentatives (key : List Bool → List Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | x :: xs => if key x ∈ xs.map key then sparseListRepresentatives key xs else x :: sparseListRepresentatives key xs

theorem sparseListRepresentatives_sublist (key : List Bool → List Bool) (xs : List (List Bool)) :
    (sparseListRepresentatives key xs).Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.slnil
  | cons x xs ih =>
    by_cases h : key x ∈ xs.map key
    · simpa [sparseListRepresentatives, h] using ih.cons x
    · simpa [sparseListRepresentatives, h] using ih.cons_cons x

theorem sparseListRepresentatives_keys (key : List Bool → List Bool) (xs : List (List Bool))
    (k : List Bool) : k ∈ (sparseListRepresentatives key xs).map key ↔ k ∈ xs.map key := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : key x ∈ xs.map key
    · simp only [sparseListRepresentatives, h, ite_true, ih, List.map_cons, List.mem_cons]
      exact ⟨Or.inr, fun e => e.elim (fun he => he ▸ h) id⟩
    · simp [sparseListRepresentatives, h, ih]

theorem sparseListRepresentatives_unique (key : List Bool → List Bool) (xs : List (List Bool)) :
    ((sparseListRepresentatives key xs).map key).Nodup := by
  induction xs with
  | nil => simp [sparseListRepresentatives]
  | cons x xs ih =>
    by_cases h : key x ∈ xs.map key
    · simpa [sparseListRepresentatives, h] using ih
    · simp [sparseListRepresentatives, h, ih, sparseListRepresentatives_keys]

def sparseListStep (f : List Bool → List Bool → List Bool) (b : Nat) :
    List (List Bool) → List (List Bool)
  | [] => []
  | a :: as =>
    if as.length ≤ b then a :: as else
      let rs := sparseListRepresentatives (f a) as
      if b < rs.length then rs else a :: rs

private theorem step_small (f : List Bool → List Bool → List Bool) (b : Nat)
    (xs : List (List Bool)) (h : xs.length ≤ b + 1) : sparseListStep f b xs = xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
    have h' : as.length ≤ b := Nat.le_of_succ_le_succ h
    simp [sparseListStep, h']

private theorem step_sublist (f : List Bool → List Bool → List Bool)
    (b : Nat) (xs : List (List Bool)) : (sparseListStep f b xs).Sublist xs := by
  cases xs with
  | nil => simp [sparseListStep]
  | cons a as =>
    by_cases h : as.length ≤ b
    · simp [sparseListStep, h]
    · by_cases h' : b < (sparseListRepresentatives (f a) as).length
      · simpa [sparseListStep, h, h'] using (sparseListRepresentatives_sublist (f a) as).cons a
      · simpa [sparseListStep, h, h'] using (sparseListRepresentatives_sublist (f a) as).cons_cons a

private theorem step_decreases (f : List Bool → List Bool → List Bool)
    (b : Nat) (xs : List (List Bool)) (h : b + 1 < xs.length) :
    (sparseListStep f b xs).length < xs.length := by
  cases xs with
  | nil => simp at h
  | cons a as =>
    have hlen := (sparseListRepresentatives_sublist (f a) as).length_le
    have hh : ¬ as.length ≤ b := by simp only [List.length_cons] at h; omega
    by_cases h' : b < (sparseListRepresentatives (f a) as).length
    · simp [sparseListStep, hh, h']
      omega
    · have hlt : (sparseListRepresentatives (f a) as).length < as.length :=
        (Nat.le_of_not_gt h').trans_lt (Nat.lt_of_not_ge hh)
      simpa [sparseListStep, hh, h'] using hlt

private theorem step_preserves (f : List Bool → List Bool → List Bool)
    (A B : Language Bool) (spec : ∀ x y, f x y ∈ B ↔ x ∈ A ∨ y ∈ A)
    (b : Nat) (xs : List (List Bool))
    (sparse : ∀ a ∈ xs, ∀ z : Finset (List Bool),
      (∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs, f a w = y) → z.card ≤ b) :
    (∃ x ∈ sparseListStep f b xs, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A := by
  constructor
  · rintro ⟨x, hx, hA⟩
    exact ⟨x, (step_sublist f b xs).subset hx, hA⟩
  · rintro ⟨x, hx, hA⟩
    by_cases hsmall : xs.length ≤ b + 1
    · exact ⟨x, by simpa [step_small f b xs hsmall] using hx, hA⟩
    cases xs with
    | nil => simp at hx
    | cons a as =>
      have hlarge : ¬ as.length ≤ b := fun h => hsmall (Nat.succ_le_succ h)
      let rs := sparseListRepresentatives (f a) as
      have yesRep (ha : a ∉ A) : ∃ w ∈ rs, w ∈ A := by
        rcases List.mem_cons.mp hx with e | hm
        · exact False.elim (ha (e ▸ hA))
        · have hit := (sparseListRepresentatives_keys (f a) as (f a x)).mpr (List.mem_map_of_mem hm)
          obtain ⟨w, hw, he⟩ := List.mem_map.mp hit
          have him : f a x ∈ B := (spec a x).mpr (Or.inr hA)
          rw [← he] at him
          exact ⟨w, hw, ((spec a w).mp him).resolve_left ha⟩
      by_cases hm : b < rs.length
      · have ha : a ∉ A := by
          intro ha
          let keys := rs.map (f a)
          have hcard : keys.toFinset.card = rs.length := by
            rw [List.toFinset_card_of_nodup (sparseListRepresentatives_unique (f a) as), List.length_map]
          have hs := sparse a List.mem_cons_self keys.toFinset (fun y hy => by
            obtain ⟨w, hw, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
            have hw' := (sparseListRepresentatives_sublist (f a) as).subset hw
            exact ⟨he ▸ (spec a w).mpr (Or.inl ha), w, List.mem_cons_of_mem _ hw', he⟩)
          omega
        simpa [sparseListStep, hlarge, show b < (sparseListRepresentatives (f a) as).length from hm] using yesRep ha
      · have he : sparseListStep f b (a :: as) = a :: rs := by
          simp [sparseListStep, hlarge, show ¬ b < (sparseListRepresentatives (f a) as).length from hm, rs]
        rw [he]
        by_cases ha : a ∈ A
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨w, hw, hA⟩ := yesRep ha
          exact ⟨w, List.mem_cons_of_mem _ hw, hA⟩

theorem sparseListRun_correct (f : List Bool → List Bool → List Bool) (b : Nat)
    (A B : Language Bool) (spec : ∀ x y, f x y ∈ B ↔ x ∈ A ∨ y ∈ A)
    (k : Nat) (xs : List (List Bool))
    (sparse : ∀ a ∈ xs, ∀ z : Finset (List Bool),
      (∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs, f a w = y) → z.card ≤ b) :
    let ys := (sparseListStep f b)^[k] xs
    ys.Sublist xs ∧ ys.length ≤ max (b + 1) (xs.length - k) ∧
      ((∃ x ∈ ys, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    dsimp only
    rw [Function.iterate_succ_apply]
    let xs' := sparseListStep f b xs
    have hsub : xs'.Sublist xs := step_sublist f b xs
    have hsparse (a : List Bool) (ha : a ∈ xs') (z : Finset (List Bool))
        (hz : ∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs', f a w = y) : z.card ≤ b :=
      sparse a (hsub.subset ha) z (fun y hy => by
        obtain ⟨hyB, w, hw, e⟩ := hz y hy
        exact ⟨hyB, w, hsub.subset hw, e⟩)
    obtain ⟨hsub', hlen, he⟩ := ih xs' hsparse
    refine ⟨hsub'.trans hsub, hlen.trans ?_, he.trans (step_preserves f A B spec b xs sparse)⟩
    by_cases hsmall : xs.length ≤ b + 1
    · have hs := hsub.length_le
      omega
    · have hs := step_decreases f b xs (by omega)
      change xs'.length < xs.length at hs
      omega

/-- The procedure uses only equality of reduction images, list operations, and the bound. -/
theorem SparsePruningAlgorithm (f : List Bool → List Bool → List Bool) :
    ∃ run : Nat → List (List Bool) → List (List Bool),
      ∀ (A B : Language Bool),
      (∀ x y, f x y ∈ B ↔ x ∈ A ∨ y ∈ A) →
      ∀ (b : Nat) (xs : List (List Bool)),
        (∀ a ∈ xs, ∀ z : Finset (List Bool),
          (∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs, f a w = y) → z.card ≤ b) →
        (run b xs).Sublist xs ∧ (run b xs).length ≤ b + 1 ∧
          ((∃ x ∈ run b xs, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  refine ⟨fun b xs => (sparseListStep f b)^[xs.length] xs, fun A B spec b xs sparse => ?_⟩
  simpa using sparseListRun_correct f b A B spec xs.length xs sparse

end PEqualNP.Outside
