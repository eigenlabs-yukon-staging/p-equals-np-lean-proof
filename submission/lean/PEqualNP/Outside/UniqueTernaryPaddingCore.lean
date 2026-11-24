import PEqualNP.Outside.UniqueTernaryFalseGadget
import PEqualNP.Outside.TernaryPaddingDegree

namespace PEqualNP.Outside.UniqueTernaryGadget
open PEqualNP.Search
open PEqualNP.Outside.TernaryGadget
  (taut taut_iff taut_eval normalized_nodup dedup_eval lift old old_inj lifted_ids
   ids_rename ids_flatMap rename_clause rename_formula extend extend_old)
open PEqualNP.Outside.OccurrenceSplit (ids ids_append)

def clean (c : Clause) : Clause :=
  if taut c then (c.map Prod.fst).dedup.map (fun i => (i,true)) else c.dedup

theorem clean_len (c : Clause) : (clean c).length ≤ c.length := by
  unfold clean
  split
  · simpa only [List.length_map] using (List.dedup_sublist (c.map Prod.fst)).length_le
  · exact (List.dedup_sublist c).length_le

theorem clean_vars (c : Clause) (i : ℕ) :
    i ∈ (clean c).map Prod.fst ↔ i ∈ c.map Prod.fst := by
  unfold clean
  split
  · simp [List.map_map,Function.comp_def,List.map_id_fun]
  · simp [List.mem_map]

theorem clean_nodup (c : Clause) : ((clean c).map Prod.fst).Nodup := by
  unfold clean
  cases h : taut c
  · simpa only [h,Bool.false_eq_true,ite_false] using normalized_nodup h
  · simpa [h,List.map_map,Function.comp_def] using List.nodup_dedup (c.map Prod.fst)

theorem taut_not_distinct {c : Clause} (h : taut c = true) : ¬ (c.map Prod.fst).Nodup := by
  intro hN
  obtain ⟨v,ha,hb⟩ := (taut_iff c).mp h
  obtain ⟨i,hi,hea⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j,hj,heb⟩ := List.mem_iff_getElem.mp hb
  have he : (c.map Prod.fst)[i]'(by simpa using hi) = (c.map Prod.fst)[j]'(by simpa using hj) := by
    rw [List.getElem_map,List.getElem_map,hea,heb]
  have e : (⟨i,by simpa using hi⟩ : Fin (c.map Prod.fst).length) = ⟨j,by simpa using hj⟩ :=
    List.nodup_iff_injective_getElem.mp hN he
  have eVal := congrArg Fin.val e
  simp only at eVal
  subst j
  rw [hea] at heb
  cases heb

theorem taut_space (c : Clause) (hC : c.length ≤ 3) (ht : taut c = true) :
    (clean c).length < 3 := by
  have hn := taut_not_distinct ht
  rw [List.nodup_iff_le_length_dedup] at hn
  simp only [List.length_map] at hn
  simp only [clean,ht,ite_true,List.length_map]
  omega

theorem clean_count (c : Clause) (i : ℕ) :
    ((clean c).map Prod.fst).count i ≤ (c.map Prod.fst).count i := by
  have hN := clean_nodup c
  by_cases hi : i ∈ (clean c).map Prod.fst
  · rw [List.nodup_iff_count_eq_one.mp hN i hi]
    exact List.count_pos_iff.mpr ((clean_vars c i).mp hi)
  · simp [List.count_eq_zero_of_not_mem hi]

def fresh (j i v : ℕ) : ℕ := 2*(21*j+7*i+v)+1

def placed (j i : ℕ) : CNF := gadget.map (List.map (lift (fresh j i)))

def added (j : ℕ) (c : Clause) : Clause :=
  (List.range (3-(clean c).length)).map (fun i => (fresh j i 0,!(taut c && i == 0)))

def block (j : ℕ) (c : Clause) : CNF :=
  [((clean c).map (lift old)) ++ added j c] ++
    (List.range (3-(clean c).length)).flatMap (placed j)

def padFrom (j : ℕ) : CNF → CNF
  | [] => []
  | c::F => block j c ++ padFrom (j+1) F

theorem fresh_inj (j i : ℕ) : Function.Injective (fresh j i) := by
  intro a b h
  unfold fresh at h
  omega

theorem placed_unique (a : Assignment) (j i : ℕ) (h : CNF.eval a (placed j i) = true) :
    ∀ v < 7, a (fresh j i v) = false := by
  unfold placed at h
  rw [rename_formula] at h
  exact unique _ h

theorem placed_extend (a : Assignment) (j i : ℕ) : CNF.eval (extend a) (placed j i) = true := by
  rw [placed,rename_formula]
  have he : extend a ∘ fresh j i = fun _ => false := by
    funext v
    have hp : (fresh j i v)%2 ≠ 0 := by unfold fresh; omega
    simp [Function.comp_def,extend,hp]
  rw [he]
  exact zero_model

theorem block_shape (j : ℕ) (c : Clause) (hC : c.length ≤ 3) :
    ∀ cl ∈ block j c, cl.length = 3 ∧ (cl.map Prod.fst).Nodup := by
  intro cl hc
  rw [block,List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [List.mem_singleton] at hc
    subst cl
    have hlen := (clean_len c).trans hC
    have hOld : (((clean c).map (lift old)).map Prod.fst).Nodup := by
      rw [lifted_ids]
      exact (clean_nodup c).map old_inj
    have hNew : ((added j c).map Prod.fst).Nodup := by
      have hf : Function.Injective (fun i => fresh j i 0) := by
        intro a b h
        change fresh j a 0 = fresh j b 0 at h
        unfold fresh at h
        omega
      simpa [added,List.map_map,Function.comp_def] using (List.nodup_range).map (f := fun i => fresh j i 0) hf
    constructor
    · simp [added,Nat.add_sub_of_le hlen]
    · rw [List.map_append,List.nodup_append]
      refine ⟨hOld,hNew,?_⟩
      intro x hx y hy hxy
      rw [lifted_ids] at hx
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
      have hn : (added j c).map Prod.fst = (List.range (3-(clean c).length)).map (fun i => fresh j i 0) := by
        simp [added,List.map_map,Function.comp_def]
      rw [hn] at hy
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hy
      unfold old fresh at hxy
      omega
  · obtain ⟨i,hi,hp⟩ := List.mem_flatMap.mp hc
    obtain ⟨cc,hcc,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hL,hN,_⟩ := shape cc hcc
    rw [List.length_map,lifted_ids]
    exact ⟨hL,hN.map (fresh_inj j i)⟩

end PEqualNP.Outside.UniqueTernaryGadget
