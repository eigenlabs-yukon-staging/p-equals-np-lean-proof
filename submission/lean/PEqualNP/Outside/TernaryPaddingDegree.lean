import PEqualNP.Outside.TernaryPadding
import PEqualNP.Outside.OccurrenceCycle
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Count
import Mathlib.Data.List.Perm.Subperm

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Search
open PEqualNP.Outside.OccurrenceSplit (ids ids_append)

def localIds (m : ℕ) : List ℕ :=
  (List.range m).map (fun i => 4*i) ++
    (List.range m).flatMap (fun i => (ids gadget).map (fun x => 4*i+x))

def offset (j x : ℕ) : ℕ := 2*(12*j+x)+1

theorem offset_inj (j : ℕ) : Function.Injective (offset j) := by
  intro a b h
  unfold offset at h
  omega

theorem local_full_bound : ∀ i ∈ localIds 3, i < 12 ∧ (localIds 3).count i ≤ 4 := by decide

theorem local_sublist (m : ℕ) (hm : m ≤ 3) : List.Sublist (localIds m) (localIds 3) := by
  have h := List.range_sublist.mpr hm
  exact (h.map _).append (h.flatMap _)

theorem local_bound (m i : ℕ) (hm : m ≤ 3) : (localIds m).count i ≤ 4 := by
  by_cases hi : i ∈ localIds m
  · have h := local_sublist m hm
    exact (List.subperm_iff_count.mp h.subperm i).trans
      ((local_full_bound i (h.subset hi)).2)
  · simp [List.count_eq_zero_of_not_mem hi]

theorem local_support (m i : ℕ) (hm : m ≤ 3) (hi : i ∈ localIds m) : i < 12 :=
  (local_full_bound i ((local_sublist m hm).subset hi)).1

theorem ids_rename (f : ℕ → ℕ) (F : CNF) :
    ids (F.map (List.map (lift f))) = (ids F).map f := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change
      ((c.map (lift f)).map Prod.fst) ++ ids (F.map (List.map (lift f))) =
        ((c.map Prod.fst) ++ ids F).map f
    rw [List.map_append,lifted_ids,ih]

theorem ids_flatMap {α : Type} (xs : List α) (f : α → CNF) :
    ids (xs.flatMap f) = xs.flatMap (fun i => ids (f i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.flatMap_cons,ids_append,ih]

private theorem map_flat_interchange {α β γ : Type} (xs : List α) (f : α → List β) (g : β → γ) :
    (xs.flatMap f).map g = xs.flatMap (fun i => (f i).map g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.map_append,ih]

theorem block_ids (j : ℕ) (cl : Clause) :
    ids (block j cl) = (cl.map Prod.fst).map old ++ (localIds (missing cl)).map (offset j) := by
  have hs : ids [cl.map (lift old) ++ added j cl] =
      ((cl.map Prod.fst).map old) ++ (List.range (missing cl)).map (fun i => fresh j i 0) := by
    change (cl.map (lift old) ++ added j cl).map Prod.fst ++ [] = _
    rw [List.append_nil,List.map_append,lifted_ids,added_ids]
  have hg : (List.range (missing cl)).flatMap (fun i => ids (place j i)) =
      (List.range (missing cl)).flatMap (fun i =>
        ((ids gadget).map (fun x => 4*i+x)).map (offset j)) := by
    apply List.flatMap_congr
    intro i _
    rw [place,ids_rename,List.map_map]
    rfl
  rw [block,ids_append,hs,ids_flatMap,hg,localIds,List.map_append,map_flat_interchange,List.map_map]
  simp only [List.append_assoc,List.map_map,Function.comp_def,offset,fresh,Nat.add_zero]

theorem aux_count (j m w : ℕ) (hm : m ≤ 3) :
    ((localIds m).map (offset j)).count w ≤ 4 := by
  by_cases hw : w ∈ (localIds m).map (offset j)
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    rw [List.count_map_of_injective _ _ (offset_inj j)]
    exact local_bound m i hm
  · simp [List.count_eq_zero_of_not_mem hw]

theorem block_count_old (j v : ℕ) (cl : Clause) :
    (ids (block j cl)).count (old v) = (cl.map Prod.fst).count v := by
  rw [block_ids,List.count_append,List.count_map_of_injective _ _ old_inj]
  have h : old v ∉ (localIds (missing cl)).map (offset j) := by
    intro hm
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hm
    unfold old offset at hi
    omega
  rw [List.count_eq_zero_of_not_mem h,Nat.add_zero]

theorem block_count_new (j w : ℕ) (hodd : w % 2 = 1) (cl : Clause) :
    (ids (block j cl)).count w ≤ 4 := by
  rw [block_ids,List.count_append]
  have h : w ∉ (cl.map Prod.fst).map old := by
    intro h
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
    unfold old at hodd
    omega
  rw [List.count_eq_zero_of_not_mem h,Nat.zero_add]
  exact aux_count j _ _ (Nat.sub_le ..)

theorem block_support_new (j w : ℕ) (hodd : w % 2 = 1) (cl : Clause)
    (hm : w ∈ ids (block j cl)) : ∃ i < 12, w = offset j i := by
  rw [block_ids,List.mem_append] at hm
  rcases hm with h | h
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
    unfold old at hodd
    omega
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact ⟨i,local_support _ _ (Nat.sub_le ..) hi,rfl⟩


theorem pad_support_new (j w : ℕ) (hodd : w % 2 = 1) (F : CNF) :
    w ∈ ids (padFrom j F) → ∃ k ≥ j, ∃ i < 12, w = offset k i := by
  induction F generalizing j with
  | nil => simp [padFrom,ids]
  | cons c F ih =>
    rw [padFrom,ids_append,List.mem_append]
    rintro (h | h)
    · obtain ⟨i,hi,e⟩ := block_support_new j w hodd c h
      exact ⟨j,Nat.le_refl _,i,hi,e⟩
    · obtain ⟨k,hk,i,hi,e⟩ := ih (j+1) h
      exact ⟨k,by omega,i,hi,e⟩

theorem pad_count_new (j w : ℕ) (hodd : w % 2 = 1) (F : CNF) :
    (ids (padFrom j F)).count w ≤ 4 := by
  induction F generalizing j with
  | nil => simp [padFrom,ids]
  | cons c F ih =>
    rw [padFrom,ids_append,List.count_append]
    by_cases h : w ∈ ids (block j c)
    · have hnone : w ∉ ids (padFrom (j+1) F) := by
        intro ht
        obtain ⟨k,hk,i,hi,he⟩ := pad_support_new (j+1) w hodd F ht
        obtain ⟨u,hu,hu'⟩ := block_support_new j w hodd c h
        unfold offset at he hu'
        omega
      rw [List.count_eq_zero_of_not_mem hnone,Nat.add_zero]
      exact block_count_new j w hodd c
    · rw [List.count_eq_zero_of_not_mem h,Nat.zero_add]
      exact ih _

theorem pad_count_old (j v : ℕ) (F : CNF) :
    (ids (padFrom j F)).count (old v) = (ids F).count v := by
  induction F generalizing j with
  | nil => rfl
  | cons c F ih =>
    rw [padFrom,ids_append,List.count_append,block_count_old,ih]
    change _ = (c.map Prod.fst ++ ids F).count v
    rw [List.count_append]

theorem pad_degree (j : ℕ) (F : CNF) (h : ∀ v, (ids F).count v ≤ 3) :
    ∀ w, (ids (padFrom j F)).count w ≤ 4 := by
  intro w
  by_cases hpar : w % 2 = 0
  · have he : old (w/2) = w := by unfold old; omega
    rw [← he,pad_count_old]
    exact (h _).trans (by decide)
  · exact pad_count_new j w (by omega) F

theorem normalize_count (F : CNF) (v : ℕ) : (ids (normalize F)).count v ≤ (ids F).count v := by
  have ids_get (F : CNF) : ids F = F.flatten.map Prod.fst := by
    simp [ids,List.flatMap_def,List.map_flatten]
  simpa only [ids_get] using List.subperm_iff_count.mp
    (((normalize_sublist F).map Prod.fst).subperm) v

def regularize (F : CNF) : CNF := padFrom 0 (normalize F)

theorem regularize_sat (F : CNF) : Satisfiable (regularize F) ↔ Satisfiable F := by
  rw [regularize,pad_sat]
  unfold Satisfiable
  simp only [normalize_eval]

end PEqualNP.Outside.TernaryGadget

open PEqualNP.Search

theorem PEqualNP.Outside.TernaryPaddingDegree :
    ∀ F : CNF, IsKCNF 3 F →
      (∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 3) →
      ∃ G : CNF,
        (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
        (∀ v, (G.flatMap (List.map Prod.fst)).count v ≤ 4) ∧
        (Satisfiable G ↔ Satisfiable F) := by
  intro F hW hD
  open PEqualNP.Outside.TernaryGadget in
  exact ⟨regularize F,pad_shape _ 0 (normalize_shape F hW),
    pad_degree _ _ (fun v => (normalize_count F v).trans (hD v)),regularize_sat F⟩
