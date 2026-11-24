import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

namespace PEqualNP.Outside.SparseImageCandidatePruning

variable {α β : Type} [DecidableEq β]

def pruneCollision : List (α × β) → Option (List (α × β))
  | [] => none
  | a :: as =>
    if a.2 ∈ as.map Prod.snd then some as
    else (pruneCollision as).map (a :: ·)

theorem no_collision (as : List (α × β)) (h : pruneCollision as = none) :
    (as.map Prod.snd).Nodup := by
  induction as with
  | nil => simp
  | cons a as ih =>
    by_cases ha : a.2 ∈ as.map Prod.snd
    · simp [pruneCollision, ha] at h
    · simp only [pruneCollision, ha, if_false, Option.map_eq_none_iff] at h
      exact List.nodup_cons.mpr ⟨ha, ih h⟩

theorem collision_sublist (as bs : List (α × β)) (h : pruneCollision as = some bs) :
    bs.Sublist as ∧ bs.length + 1 = as.length := by
  induction as generalizing bs with
  | nil => simp [pruneCollision] at h
  | cons a as ih =>
    by_cases ha : a.2 ∈ as.map Prod.snd
    · have he : as = bs := by simpa [pruneCollision, ha] using h
      subst bs
      exact ⟨List.Sublist.cons _ (List.Sublist.refl _),rfl⟩
    · obtain ⟨us,he,hs⟩ := Option.map_eq_some_iff.mp (by simpa [pruneCollision, ha] using h)
      obtain ⟨hu,hlen⟩ := ih us he
      subst bs
      exact ⟨List.Sublist.cons_cons _ hu, by simp only [List.length_cons]; omega⟩

theorem collision_correct (G : α → Prop) (J : β → Prop) (pivot : α)
    (as bs : List (α × β)) (h : pruneCollision as = some bs)
    (hrel : ∀ q ∈ as, J q.2 ↔ G pivot ∨ G q.1) :
    (G pivot ∨ ∃ q ∈ bs, G q.1) ↔ G pivot ∨ ∃ q ∈ as, G q.1 := by
  induction as generalizing bs with
  | nil => simp [pruneCollision] at h
  | cons a as ih =>
    by_cases ha : a.2 ∈ as.map Prod.snd
    · have he : as = bs := by simpa [pruneCollision, ha] using h
      subst bs
      obtain ⟨b,hb,heb⟩ := List.mem_map.mp ha
      constructor
      · rintro (hp | ⟨q,hq,hg⟩)
        · exact Or.inl hp
        · exact Or.inr ⟨q,List.mem_cons_of_mem _ hq,hg⟩
      · rintro (hp | ⟨q,hq,hg⟩)
        · exact Or.inl hp
        · rcases List.mem_cons.mp hq with rfl | hq
          · have hj := (hrel q List.mem_cons_self).mpr (Or.inr hg)
            rw [← heb] at hj
            rcases (hrel b (List.mem_cons_of_mem _ hb)).mp hj with hp | hgood
            · exact Or.inl hp
            · exact Or.inr ⟨b,hb,hgood⟩
          · exact Or.inr ⟨q,hq,hg⟩
    · obtain ⟨us,he,hs⟩ := Option.map_eq_some_iff.mp (by simpa [pruneCollision, ha] using h)
      subst bs
      have hic := ih us he (fun q hq => hrel q (List.mem_cons_of_mem _ hq))
      simp only [List.exists_mem_cons_iff]
      by_cases hp : G pivot
      · simp [hp]
      · simp only [hp, false_or] at hic ⊢
        exact or_congr Iff.rfl hic

def prune (pivot : α) (as : List (α × β)) : List α :=
  match pruneCollision as with
  | none => as.map Prod.fst
  | some bs => pivot :: bs.map Prod.fst

theorem prune_sublist (pivot : α) (as : List (α × β)) :
    (prune pivot as).Sublist (pivot :: as.map Prod.fst) ∧
      (prune pivot as).length + 1 = as.length + 1 := by
  cases h : pruneCollision as with
  | none =>
    simp only [prune, h]
    exact ⟨List.Sublist.cons _ (List.Sublist.refl _), by simp⟩
  | some bs =>
    simp only [prune, h]
    obtain ⟨hs,hlen⟩ := collision_sublist as bs h
    exact ⟨List.Sublist.cons_cons _ (hs.map _), by simp only [List.length_cons, List.length_map]; omega⟩

theorem prune_preserves (G : α → Prop) (S : Finset β) (pivot : α) (as : List (α × β))
    (hc : S.card < as.length) (hrel : ∀ q ∈ as, q.2 ∈ S ↔ G pivot ∨ G q.1) :
    (∃ x ∈ prune pivot as, G x) ↔ G pivot ∨ ∃ q ∈ as, G q.1 := by
  classical
  cases h : pruneCollision as with
  | none =>
    have hno : ¬G pivot := by
      intro hp
      have hsub : (as.map Prod.snd).toFinset ⊆ S := by
        intro y hy
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
        exact (hrel q hq).mpr (Or.inl hp)
      have hb := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup (no_collision as h), List.length_map] at hb
      omega
    simp [prune,h,hno]
  | some bs => simpa [prune,h] using collision_correct G (· ∈ S) pivot as bs h hrel

end PEqualNP.Outside.SparseImageCandidatePruning

open PEqualNP.Outside.SparseImageCandidatePruning

theorem PEqualNP.Outside.SparseImageCandidatePruning :
    ∀ (α β : Type) [DecidableEq β],
      ∃ prune : α → List (α × β) → List α,
        ∀ (pivot : α) (as : List (α × β)),
          (prune pivot as).Sublist (pivot :: as.map Prod.fst) ∧
          (prune pivot as).length + 1 = as.length + 1 ∧
          ∀ (G : α → Prop) (S : Finset β),
            S.card < as.length → (∀ q ∈ as, q.2 ∈ S ↔ G pivot ∨ G q.1) →
              ((∃ x ∈ prune pivot as, G x) ↔ G pivot ∨ ∃ q ∈ as, G q.1) := by
  intro α β inst
  exact ⟨prune, fun pivot as => ⟨(prune_sublist pivot as).1, (prune_sublist pivot as).2,
    fun G S => prune_preserves G S pivot as⟩⟩
