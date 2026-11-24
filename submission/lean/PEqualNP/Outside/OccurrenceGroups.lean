import PEqualNP.Outside.OccurrenceNumbering
import PEqualNP.Outside.ParsimoniousTableau
import PEqualNP.Outside.TableauWidth

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Search

def oldAt (F : CNF) (i : ℕ) : ℕ := (F.flatten[i]?.getD (0,false)).1
def group (F : CNF) (v : ℕ) : List ℕ :=
  (List.range F.flatten.length).filter (fun i => oldAt F i == v)

def links (F : CNF) : CNF := (ids F).dedup.flatMap (fun v => cycle (group F v))
def split (F : CNF) : CNF := main 0 F ++ links F

theorem ids_flatten (F : CNF) : ids F = F.flatten.map Prod.fst := by
  simp [ids,List.flatMap_def,List.map_flatten]

theorem group_mem (F : CNF) (v i : ℕ) :
    i ∈ group F v ↔ i < F.flatten.length ∧ oldAt F i = v := by
  simp [group]

theorem old_in_ids (F : CNF) (i : ℕ) (hi : i < F.flatten.length) : oldAt F i ∈ ids F := by
  rw [ids_flatten]
  exact List.mem_map.mpr ⟨F.flatten[i],List.getElem_mem hi,by simp [oldAt,List.getElem?_eq_getElem hi]⟩

theorem mentioned_has_index (F : CNF) {v : ℕ} (hv : v ∈ ids F) : ∃ i, i ∈ group F v := by
  rw [ids_flatten] at hv
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
  obtain ⟨i,hi,h⟩ := List.mem_iff_getElem.mp hl
  exact ⟨i,(group_mem F _ _).mpr ⟨hi,by simp [oldAt,List.getElem?_eq_getElem hi,h]⟩⟩

theorem links_eval (σ : Assignment) (F : CNF) :
    CNF.eval σ (links F) = true ↔
      ∀ v ∈ ids F, ∀ i ∈ group F v, ∀ j ∈ group F v, σ i = σ j := by
  simp only [links,CNF.eval,List.all_eq_true,List.mem_flatMap,List.mem_dedup]
  constructor
  · intro h v hv
    apply (cycle_eval σ (group F v)).mp
    exact List.all_eq_true.mpr (fun c hc => h c ⟨v,hv,hc⟩)
  · rintro h c ⟨v,hv,hc⟩
    exact List.all_eq_true.mp ((cycle_eval σ (group F v)).mpr (h v hv)) _ hc

theorem split_eval (σ : Assignment) (F : CNF) :
    CNF.eval σ (split F) = true ↔ CNF.eval σ (main 0 F) = true ∧ CNF.eval σ (links F) = true := by
  simp only [split,CNF.eval,List.all_append,Bool.and_eq_true_iff]

theorem group_count (F : CNF) (v i : ℕ) :
    (group F v).count i = if i ∈ group F v then 1 else 0 := by
  have hn : (group F v).Nodup := List.Nodup.filter _ (List.nodup_range ..)
  exact List.Nodup.count hn

theorem links_count (F : CNF) (i : ℕ) : (ids (links F)).count i ≤ 2 := by
  let vs := (ids F).dedup
  let g := fun v => cycle (group F v)
  have bound : ∀ l : List ℕ, (ids (l.flatMap g)).count i ≤ 2*l.count (oldAt F i) := by
    intro l
    induction l with
    | nil => simp [ids]
    | cons v l ih =>
      rw [List.flatMap_cons,ids_append,List.count_append,cycle_count,List.count_cons]
      rw [group_count]
      by_cases hv : v = oldAt F i
      · subst v
        split <;> simp <;> omega
      · have hnot : i ∉ group F v := fun hi => hv ((group_mem F v i).mp hi).2.symm
        simp [hnot,beq_iff_eq,hv,Ne.symm hv]
        exact ih
  have h := bound vs
  have hn := (List.nodup_iff_count_le_one.mp (List.nodup_dedup (ids F))) (oldAt F i)
  unfold links
  exact h.trans (Nat.mul_le_mul_left _ hn)

theorem links_support (F : CNF) (i : ℕ) (hi : i ∈ ids (links F)) : i < F.flatten.length := by
  unfold links ids at hi
  simp only [List.flatMap_assoc,List.mem_flatMap,List.mem_dedup] at hi
  obtain ⟨v,_,hv⟩ := hi
  have hc : 0 < (ids (cycle (group F v))).count i := List.count_pos_iff.mpr (List.mem_flatMap.mpr hv)
  rw [cycle_count] at hc
  have hm := List.count_pos_iff.mp (show 0 < (group F v).count i by omega)
  exact ((group_mem F v i).mp hm).1

theorem split_support (F : CNF) (i : ℕ) : i ∈ ids (split F) ↔ i < F.flatten.length := by
  rw [split,ids_append,main_ids,List.mem_append,List.mem_range]
  exact ⟨fun h => h.elim id (links_support F i),Or.inl⟩

theorem split_count (F : CNF) (i : ℕ) : (ids (split F)).count i ≤ 3 := by
  rw [split,ids_append,List.count_append,main_ids]
  have h₁ := List.nodup_iff_count_le_one.mp (List.nodup_range (n := F.flatten.length)) i
  have h₂ := links_count F i
  omega

end PEqualNP.Outside.OccurrenceSplit
