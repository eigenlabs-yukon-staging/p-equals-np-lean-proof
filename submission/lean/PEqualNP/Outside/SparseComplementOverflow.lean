import PEqualNP.Outside.SparseImageCandidatePruning

namespace PEqualNP.Outside.SparseComplementOverflow

open PEqualNP.Outside.SparseImageCandidatePruning (pruneCollision no_collision collision_sublist)

variable {α β : Type} [DecidableEq β]

def reduce (cap : ℕ) (as : List (α × β)) : Option (List α) :=
  if as.length ≤ cap then some (as.map Prod.fst)
  else (pruneCollision as).map (List.map Prod.fst)

theorem drop_preserves (G : α → Prop) (J : β → Prop) (as bs : List (α × β))
    (h : pruneCollision as = some bs) (hrel : ∀ q ∈ as, J q.2 ↔ G q.1) :
    (∃ q ∈ bs, G q.1) ↔ ∃ q ∈ as, G q.1 := by
  induction as generalizing bs with
  | nil => simp [pruneCollision] at h
  | cons a as ih =>
    by_cases ha : a.2 ∈ as.map Prod.snd
    · have he : as = bs := by simpa [pruneCollision,ha] using h
      subst bs
      obtain ⟨b,hb,he⟩ := List.mem_map.mp ha
      constructor
      · rintro ⟨q,hq,hg⟩
        exact ⟨q,List.mem_cons_of_mem _ hq,hg⟩
      · rintro ⟨q,hq,hg⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · have hj := (hrel q List.mem_cons_self).mpr hg
          rw [← he] at hj
          exact ⟨b,hb,(hrel b (List.mem_cons_of_mem _ hb)).mp hj⟩
        · exact ⟨q,hq,hg⟩
    · obtain ⟨us,he,hs⟩ := Option.map_eq_some_iff.mp (by simpa [pruneCollision,ha] using h)
      subst bs
      have hi := ih us he (fun q hq => hrel q (List.mem_cons_of_mem _ hq))
      simp only [List.exists_mem_cons_iff,hi]

theorem reduce_correct (G : α → Prop) (S : Finset β) (cap : ℕ) (as : List (α × β))
    (hcard : S.card ≤ cap) (hrel : ∀ q ∈ as, q.2 ∈ S ↔ ¬ G q.1) :
    match reduce cap as with
    | none => ∃ q ∈ as, G q.1
    | some bs => bs.Sublist (as.map Prod.fst) ∧ bs.length ≤ max cap (as.length-1) ∧
        ((∃ y ∈ bs, G y) ↔ ∃ q ∈ as, G q.1) := by
  classical
  by_cases hcap : as.length ≤ cap
  · simp only [reduce,hcap,if_true]
    refine ⟨List.Sublist.refl _, ?_, ?_⟩
    · simpa only [List.length_map] using hcap.trans (le_max_left _ _)
    · simp
  · cases h : pruneCollision as with
    | none =>
      simp only [reduce,hcap,if_false,h,Option.map_none]
      by_contra hno
      have hsub : (as.map Prod.snd).toFinset ⊆ S := by
        intro y hy
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
        exact (hrel q hq).mpr (fun hg => hno ⟨q,hq,hg⟩)
      have hl := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup (no_collision as h),List.length_map] at hl
      omega
    | some bs =>
      simp only [reduce,hcap,if_false,h,Option.map_some]
      obtain ⟨hsub,hlen⟩ := collision_sublist as bs h
      refine ⟨hsub.map _, by simp only [List.length_map]; omega, ?_⟩
      have hi : (∃ q ∈ bs, G q.1) ↔ ∃ q ∈ as, G q.1 :=
        drop_preserves G (· ∉ S) as bs h (fun q hq => by simp [hrel q hq])
      simpa using hi

end PEqualNP.Outside.SparseComplementOverflow

open PEqualNP.Outside.SparseComplementOverflow

theorem PEqualNP.Outside.SparseComplementOverflow :
    ∀ (α β : Type) [DecidableEq β],
      ∃ reduce : ℕ → List (α × β) → Option (List α),
        ∀ (G : α → Prop) (S : Finset β) (cap : ℕ) (as : List (α × β)),
          S.card ≤ cap → (∀ q ∈ as, q.2 ∈ S ↔ ¬ G q.1) →
          match reduce cap as with
          | none => ∃ q ∈ as, G q.1
          | some bs => bs.Sublist (as.map Prod.fst) ∧ bs.length ≤ max cap (as.length-1) ∧
              ((∃ y ∈ bs, G y) ↔ ∃ q ∈ as, G q.1) := by
  intro α β inst
  exact ⟨reduce,reduce_correct⟩
