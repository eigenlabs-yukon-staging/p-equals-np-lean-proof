import PEqualNP.Outside.UniqueTernaryPaddingSemantics

namespace PEqualNP.Outside.UniqueTernaryGadget
open PEqualNP.Search
open PEqualNP.Outside.TernaryGadget (old old_inj lifted_ids ids_rename ids_flatMap)
open PEqualNP.Outside.OccurrenceSplit (ids ids_append)

def localIds (m : ℕ) : List ℕ :=
  (List.range m).map (fun i => 7*i) ++
    (List.range m).flatMap (fun i => (ids gadget).map (fun v => 7*i+v))

def offset (j k : ℕ) : ℕ := 2*(21*j+k)+1

theorem local_support (m : ℕ) (hm : m ≤ 3) : ∀ v ∈ localIds m, v < 21 := by
  interval_cases m <;> decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
theorem local_count (m : ℕ) (hm : m ≤ 3) : ∀ v ∈ localIds m, (localIds m).count v ≤ 5 := by
  interval_cases m <;> decide

theorem offset_inj (j : ℕ) : Function.Injective (offset j) := by
  intro a b h
  unfold offset at h
  omega

private theorem map_flat {α β γ : Type} (xs : List α) (f : α → List β) (g : β → γ) :
    (xs.flatMap f).map g = xs.flatMap (fun i => (f i).map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.map_append,ih]

theorem block_ids (j : ℕ) (c : Clause) :
    ids (block j c) = ((clean c).map Prod.fst).map old ++ (localIds (3-(clean c).length)).map (offset j) := by
  have hAdd : (added j c).map Prod.fst =
      (List.range (3-(clean c).length)).map (fun i => fresh j i 0) := by
    simp [added,List.map_map,Function.comp_def]
  have hLeft : ids [((clean c).map (PEqualNP.Outside.TernaryGadget.lift old)) ++ added j c] =
      ((clean c).map Prod.fst).map old ++ (List.range (3-(clean c).length)).map (fun i => fresh j i 0) := by
    change _ ++ [] = _
    rw [List.append_nil,List.map_append,lifted_ids,hAdd]
  have hRight : (List.range (3-(clean c).length)).flatMap (fun i => ids (placed j i)) =
      (List.range (3-(clean c).length)).flatMap
        (fun i => ((ids gadget).map (fun k => 7*i+k)).map (offset j)) := by
    apply List.flatMap_congr
    intro i _
    rw [placed,ids_rename,List.map_map]
    rfl
  rw [block,ids_append,hLeft,ids_flatMap,hRight,localIds,List.map_append,map_flat,List.map_map]
  simp only [List.append_assoc,List.map_map,Function.comp_def,offset,fresh,Nat.add_zero]

theorem block_count_old (j v : ℕ) (c : Clause) :
    (ids (block j c)).count (old v) ≤ (c.map Prod.fst).count v := by
  rw [block_ids,List.count_append,List.count_map_of_injective _ _ old_inj]
  have hh : old v ∉ (localIds (3-(clean c).length)).map (offset j) := by
    intro h
    obtain ⟨k,_,he⟩ := List.mem_map.mp h
    unfold old offset at he
    omega
  rw [List.count_eq_zero_of_not_mem hh,Nat.add_zero]
  exact clean_count c v

theorem block_new {j w : ℕ} (c : Clause) (ho : w % 2 = 1) (hw : w ∈ ids (block j c)) :
    ∃ k ∈ localIds (3-(clean c).length), w = offset j k := by
  rw [block_ids,List.mem_append] at hw
  rcases hw with h | h
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
    simp [old] at ho
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    exact ⟨k,hk,rfl⟩

theorem block_count_new (j w : ℕ) (c : Clause) (ho : w % 2 = 1) (hw : w ∈ ids (block j c)) :
    (ids (block j c)).count w ≤ 5 := by
  obtain ⟨k,hk,rfl⟩ := block_new c ho hw
  have hh : offset j k ∉ ((clean c).map Prod.fst).map old := by
    intro h
    obtain ⟨x,_,he⟩ := List.mem_map.mp h
    unfold offset old at he
    omega
  rw [block_ids,List.count_append,List.count_eq_zero_of_not_mem hh,Nat.zero_add,
    List.count_map_of_injective _ _ (offset_inj j)]
  exact local_count _ (Nat.sub_le ..) k hk

theorem pad_new (F : CNF) (j w : ℕ) (ho : w % 2 = 1) (hw : w ∈ ids (padFrom j F)) :
    ∃ l ≥ j, ∃ k < 21, w = offset l k := by
  induction F generalizing j with
  | nil => simp [padFrom,ids] at hw
  | cons c F ih =>
    rw [padFrom,ids_append,List.mem_append] at hw
    rcases hw with h | h
    · obtain ⟨k,hk,he⟩ := block_new c ho h
      exact ⟨j,Nat.le_refl _,k,local_support _ (Nat.sub_le ..) k hk,he⟩
    · obtain ⟨l,hl,k,hk,he⟩ := ih (j+1) h
      exact ⟨l,by omega,k,hk,he⟩

theorem pad_count_new (F : CNF) (j w : ℕ) (ho : w % 2 = 1) :
    (ids (padFrom j F)).count w ≤ 5 := by
  induction F generalizing j with
  | nil => simp [padFrom,ids]
  | cons c F ih =>
    rw [padFrom,ids_append,List.count_append]
    by_cases hw : w ∈ ids (block j c)
    · obtain ⟨k,hk,he⟩ := block_new c ho hw
      have hn : w ∉ ids (padFrom (j+1) F) := by
        intro hm
        obtain ⟨l,hl,a,ha,he'⟩ := pad_new F (j+1) w ho hm
        have hBound := local_support _ (Nat.sub_le ..) k hk
        unfold offset at he he'
        omega
      rw [List.count_eq_zero_of_not_mem hn,Nat.add_zero]
      exact block_count_new j w c ho hw
    · rw [List.count_eq_zero_of_not_mem hw,Nat.zero_add]
      exact ih _

theorem pad_count_old (F : CNF) (j v : ℕ) : (ids (padFrom j F)).count (old v) ≤ (ids F).count v := by
  induction F generalizing j with
  | nil => simp [padFrom,ids]
  | cons c F ih =>
    rw [padFrom,ids_append,List.count_append]
    change _ ≤ (c.map Prod.fst ++ ids F).count v
    rw [List.count_append]
    exact Nat.add_le_add (block_count_old j v c) (ih (j+1))

theorem pad_degree (F : CNF) (j : ℕ) (hF : ∀ v, (ids F).count v ≤ 5) :
    ∀ w, (ids (padFrom j F)).count w ≤ 5 := by
  intro w
  by_cases he : w % 2 = 0
  · have hw : old (w/2) = w := by unfold old; omega
    rw [← hw]
    exact (pad_count_old F j _).trans (hF _)
  · exact pad_count_new F j w (by omega)

end PEqualNP.Outside.UniqueTernaryGadget
