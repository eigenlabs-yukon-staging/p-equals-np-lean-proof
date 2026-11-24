import PEqualNP.Outside.SparseCoHardImpliesCollapse
import PEqualNP.Library.L009

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool

private noncomputable def boundedTuples (s : Finset Word) : Nat → Finset (List Word)
  | 0 => {[]}
  | k + 1 => insert [] ((s.product (boundedTuples s k)).image fun p => p.1 :: p.2)

private theorem mem_boundedTuples (s : Finset Word) (k : Nat) (xs : List Word)
    (h : xs.length ≤ k) (hx : ∀ x ∈ xs, x ∈ s) : xs ∈ boundedTuples s k := by
  classical
  induction k generalizing xs with
  | zero =>
    have e : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [boundedTuples, e]
  | succ k ih =>
    cases xs with
    | nil => simp [boundedTuples]
    | cons a as =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(a, as), Finset.mem_product.mpr ⟨hx a List.mem_cons_self, ?_⟩, rfl⟩
      exact ih as (by simpa using h) (fun x hm => hx x (List.mem_cons_of_mem _ hm))

private theorem boundedTuples_card (s : Finset Word) (k : Nat) :
    (boundedTuples s k).card ≤ (s.card + 1) ^ k := by
  classical
  induction k with
  | zero => simp [boundedTuples]
  | succ k ih =>
    let t := (s.product (boundedTuples s k)).image (fun p => p.1 :: p.2)
    have h₁ : t.card ≤ s.card * (boundedTuples s k).card := by
      exact Finset.card_image_le.trans_eq (Finset.card_product _ _)
    have h₂ : (insert [] t).card ≤ t.card + 1 := Finset.card_insert_le _ _
    have h₃ : 1 ≤ (s.card + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    change (insert [] t).card ≤ _
    rw [pow_succ']
    have h₄ := Nat.mul_le_mul_left s.card ih
    rw [Nat.add_mul, Nat.one_mul]
    omega

noncomputable def acceptedShort (B : Language Bool) (n : Nat) : Finset Word := by
  classical
  exact ((Finset.range (2 ^ (n+1))).image cand).filter (fun w => w ∈ B ∧ w.length ≤ n)

theorem mem_acceptedShort (B : Language Bool) (n : Nat) (w : Word)
    (hw : w ∈ B) (hl : w.length ≤ n) : w ∈ acceptedShort B n := by
  classical
  have hi := idx_lt_of_length_le hl
  have hm : w ∈ (Finset.range (2 ^ (n+1))).image cand :=
    Finset.mem_image.mpr ⟨idx w, Finset.mem_range.mpr (by omega), cand_idx w⟩
  unfold acceptedShort
  exact Finset.mem_filter.mpr ⟨hm, hw, hl⟩

theorem acceptedShort_spec (B : Language Bool) (n : Nat) (w : Word)
    (hw : w ∈ acceptedShort B n) : w ∈ B ∧ w.length ≤ n := by
  classical
  unfold acceptedShort at hw
  exact (Finset.mem_filter.mp hw).2

private theorem member_length (xs : List Word) (w : Word) (hw : w ∈ xs) :
    w.length ≤ (encodeFrontier xs).length := by
  induction xs with
  | nil => simp at hw
  | cons x xs ih =>
    change w.length ≤ (pairB x (encodeFrontier xs)).length
    rw [pairB_length]
    rcases List.mem_cons.mp hw with rfl | hm
    · omega
    · have h := ih hm; omega

private def conjunctiveTarget (B : Language Bool) (k : Nat) : Language Bool :=
  {s | ∃ xs : List Word, xs.length ≤ k ∧ (∀ x ∈ xs, x ∈ B) ∧ s = encodeFrontier xs}

private theorem encodeFrontier_injective : Function.Injective encodeFrontier := by
  intro xs
  induction xs with
  | nil =>
    intro ys e
    cases ys with
    | nil => rfl
    | cons y ys => exact False.elim (encodeFrontier_cons_ne y ys e.symm)
  | cons x xs ih =>
    intro ys e
    cases ys with
    | nil => exact False.elim (encodeFrontier_cons_ne x xs e)
    | cons y ys =>
      have ep : pairB x (encodeFrontier xs) = pairB y (encodeFrontier ys) := e
      have hc := congrArg unpairB ep
      rw [unpairB_pairB, unpairB_pairB] at hc
      have hxy : x = y := congrArg Prod.fst hc
      have ht := ih (congrArg Prod.snd hc)
      simpa only [hxy, ht]

private theorem conjunctiveTarget_sparse (B : Language Bool) (q : Polynomial Nat) (k : Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n) :
    ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ conjunctiveTarget B k ∧ y.length ≤ n) →
        ys.card ≤ ((q + 1) ^ k).eval n := by
  classical
  intro n ys h
  let s := acceptedShort B n
  let t := (boundedTuples s k).image encodeFrontier
  have hsub : ys ⊆ t := by
    intro w hw
    obtain ⟨⟨xs, hl, hx, rfl⟩, hn⟩ := h w hw
    exact Finset.mem_image.mpr ⟨xs, mem_boundedTuples s k xs hl
      (fun x hx' => mem_acceptedShort B n x (hx x hx') ((member_length xs x hx').trans hn)), rfl⟩
  have hs : s.card ≤ q.eval n := sparse n s (acceptedShort_spec B n)
  have ht : t.card ≤ (s.card + 1) ^ k :=
    Finset.card_image_le.trans (boundedTuples_card s k)
  exact (Finset.card_le_card hsub).trans (ht.trans (by
    simpa using Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) k))

private theorem conjunctive_reduction (A B : Language Bool) (k : Nat)
    (queries : Word → List Word) (hf : ComputableInPolyTime (fun x => x) (fun x => x)
      (fun x => encodeFrontier (queries x)))
    (width : ∀ x, (queries x).length ≤ k)
    (spec : ∀ x, x ∈ A ↔ ∀ y ∈ queries x, y ∈ B) :
    PolyTimeReducible A (conjunctiveTarget B k) := by
  refine ⟨fun x => encodeFrontier (queries x), hf, fun x => ?_⟩
  exact (spec x).trans ⟨fun h => ⟨queries x, width x, h, rfl⟩, fun ⟨ys, _, hy, he⟩ => by
    rw [encodeFrontier_injective he]
    exact hy⟩

/-- A fixed-width conjunctive reduction of a pinned NP-hard or coNP-hard language to
a sparse target compiles into an ordinary many-one reduction to a sparse tuple language. -/
theorem BoundedConjunctiveSparseCollapse (A B : Language Bool) (hA : NPHard A ∨ ∀ L ∈ coNP, PolyTimeReducible L A)
    (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n)
    (k : Nat) (queries : Word → List Word)
    (hf : ComputableInPolyTime (fun x => x) (fun x => x)
      (fun x => (queries x).foldr (fun a b => List.replicate a.length true ++ false :: (a ++ b)) []))
    (width : ∀ x, (queries x).length ≤ k)
    (spec : ∀ x, x ∈ A ↔ ∀ y ∈ queries x, y ∈ B) :
    P = NP := by
  have hred := conjunctive_reduction A B k queries hf width spec
  have hs := conjunctiveTarget_sparse B q k sparse
  rcases hA with hA | hA
  · exact SparseHardImpliesCollapse _ (fun L hL => L009 L A _ (hA L hL) hred) ((q + 1) ^ k) hs
  · exact SparseCoHardImpliesCollapse _ (fun L hL => L009 L A _ (hA L hL) hred) ((q + 1) ^ k) hs

end PEqualNP.Outside
