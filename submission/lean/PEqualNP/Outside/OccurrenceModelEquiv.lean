import PEqualNP.Outside.OccurrenceGroups

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Search
open PEqualNP.Outside.OneHot (Models Mentioned extend eval_restrict width_append width_flatMap)

def pull (F : CNF) (τ : Assignment) : Assignment :=
  fun i => τ (oldAt F i)

def push (F : CNF) (σ : Assignment) : Assignment :=
  fun v => σ ((group F v).headD 0)

theorem head_in_group (F : CNF) {v : ℕ} (hv : v ∈ ids F) :
    (group F v).headD 0 ∈ group F v := by
  obtain ⟨i,hi⟩ := mentioned_has_index F hv
  cases h : group F v with
  | nil => rw [h] at hi; simp at hi
  | cons x xs => simp

theorem pull_push (F : CNF) (σ : Assignment) (hx : CNF.eval σ (links F) = true)
    (i : ℕ) (hi : i < F.flatten.length) : pull F (push F σ) i = σ i := by
  let v := oldAt F i
  have hv : v ∈ ids F := old_in_ids F i hi
  have hgroup := (links_eval σ F).mp hx v hv
    ((group F v).headD 0) (head_in_group F hv) i ((group_mem F v i).mpr ⟨hi,rfl⟩)
  exact hgroup

theorem push_pull (F : CNF) (τ : Assignment) {v : ℕ} (hv : v ∈ ids F) :
    push F (pull F τ) v = τ v := by
  change τ (oldAt F ((group F v).headD 0)) = τ v
  rw [((group_mem F v _).mp (head_in_group F hv)).2]

theorem eval_pull (F : CNF) (τ : Assignment) :
    CNF.eval (pull F τ) (split F) = CNF.eval τ F := by
  have h1 : CNF.eval (pull F τ) (main 0 F) = CNF.eval τ F :=
    eval_main _ _ _ _ (fun i _ => by simp [pull,oldAt])
  have h2 : CNF.eval (pull F τ) (links F) = true := by
    apply (links_eval ..).mpr
    intro v _ i hi j hj
    simp [pull,((group_mem F v i).mp hi).2,((group_mem F v j).mp hj).2]
  have happ : CNF.eval (pull F τ) (split F) =
      (CNF.eval (pull F τ) (main 0 F) && CNF.eval (pull F τ) (links F)) := by
    simp [split,CNF.eval,List.all_append]
  rw [happ,h1,h2,Bool.and_true]

def liftModel (F : CNF) (m : Models F) : Models (split F) :=
  ⟨fun i => pull F (extend F m.1) i.1,
    (eval_restrict ..).trans ((eval_pull ..).trans m.2)⟩

def lowerModel (F : CNF) (m : Models (split F)) : Models F := by
  let σ := extend (split F) m.1
  have h := (split_eval σ F).mp m.2
  refine ⟨fun v => push F σ v.1,(eval_restrict ..).trans ?_⟩
  have ha : Agreement σ (push F σ) 0 F.flatten := by
    intro i hi
    rw [Nat.zero_add]
    exact (pull_push F σ h.2 i hi).symm
  exact (eval_main _ _ _ _ ha).symm.trans h.1

theorem read_model {F : CNF} (m : Models F) {i : ℕ} (hi : Mentioned F i) :
    extend F m.1 i = m.1 ⟨i,hi⟩ := dite_eq_left hi

theorem lift_lower (F : CNF) (m : Models (split F)) : liftModel F (lowerModel F m) = m := by
  apply Subtype.ext
  funext i
  let σ := extend (split F) m.1
  have h := (split_eval σ F).mp m.2
  have hi := (split_support F i.1).mp i.2
  have hv := old_in_ids F i.1 hi
  change extend F (lowerModel F m).1 (oldAt F i.1) = m.1 i
  rw [read_model (lowerModel F m) hv]
  change pull F (push F σ) i.1 = _
  exact (pull_push F σ h.2 i.1 hi).trans (read_model m i.2)

theorem lower_lift (F : CNF) (m : Models F) : lowerModel F (liftModel F m) = m := by
  apply Subtype.ext
  funext v
  let i := (group F v.1).headD 0
  have hi := (group_mem F v.1 i).mp (head_in_group F v.2)
  have hmem := (split_support F i).mpr hi.1
  change extend (split F) (liftModel F m).1 i = m.1 v
  rw [read_model (liftModel F m) hmem]
  change extend F m.1 (oldAt F i) = _
  rw [hi.2]
  exact read_model m v.2

def modelsEquiv (F : CNF) : Models F ≃ Models (split F) where
  toFun := liftModel F
  invFun := lowerModel F
  left_inv := lower_lift F
  right_inv := lift_lower F

theorem chain_width (a b : ℕ) (xs : List ℕ) : IsKCNF 3 (chain a b xs) := by
  induction xs generalizing b with
  | nil => simp [chain,IsKCNF,arc]
  | cons x xs ih =>
    have h := ih x
    simpa [chain,IsKCNF,arc] using h

theorem split_width (F : CNF) (h : IsKCNF 3 F) : IsKCNF 3 (split F) := by
  rw [split,width_append,links,width_flatMap]
  refine ⟨main_width 3 0 F h,fun v _ => ?_⟩
  cases group F v with
  | nil => simp [cycle,IsKCNF]
  | cons x xs => exact chain_width x x xs

end PEqualNP.Outside.OccurrenceSplit

open PEqualNP.Search

theorem PEqualNP.Outside.OccurrenceModelEquiv :
    ∀ φ : CNF, IsKCNF 3 φ →
      ∃ ψ : CNF, IsKCNF 3 ψ ∧ (∀ i : ℕ, (ψ.flatMap (List.map Prod.fst)).count i ≤ 3) ∧
        Nonempty (
          {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
            CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
              then a ⟨i,h⟩ else false) φ = true} ≃
          {b : {i : ℕ // i ∈ ψ.flatMap (List.map Prod.fst)} → Bool //
            CNF.eval (fun i => if h : i ∈ ψ.flatMap (List.map Prod.fst)
              then b ⟨i,h⟩ else false) ψ = true}) := by
  open PEqualNP.Outside.OccurrenceSplit in
  exact fun φ h => ⟨split φ,split_width φ h,split_count φ,⟨modelsEquiv φ⟩⟩
