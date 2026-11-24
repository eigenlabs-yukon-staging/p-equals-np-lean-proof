import PEqualNP.Outside.UniqueTernaryPaddingCore

namespace PEqualNP.Outside.UniqueTernaryGadget
open PEqualNP.Search
open PEqualNP.Outside.TernaryGadget
  (taut taut_eval dedup_eval lift old old_inj lifted_ids
   ids_rename ids_flatMap rename_clause extend extend_old)
open PEqualNP.Outside.OccurrenceSplit (ids ids_append)

theorem block_forces (a : Assignment) (j : ℕ) (cl : Clause)
    (h : CNF.eval a (block j cl) = true) (i : ℕ) (hi : i < 3-(clean cl).length) :
    ∀ v < 7, a (fresh j i v) = false := by
  apply placed_unique
  simp only [CNF.eval,List.all_eq_true] at h ⊢
  intro c hc
  exact h c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hc⟩))

theorem block_sound (a : Assignment) (j : ℕ) (c : Clause)
    (h : CNF.eval a (block j c) = true) : Clause.eval (a ∘ old) c = true := by
  cases ht : taut c
  · have hm : Clause.eval a ((clean c).map (lift old) ++ added j c) = true :=
      List.all_eq_true.mp h _ (List.mem_append_left _ (by simp))
    have hn : Clause.eval a (added j c) = false := by
      cases e : Clause.eval a (added j c)
      · rfl
      · obtain ⟨l,hl,he⟩ := List.any_eq_true.mp e
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
        simp [Literal.eval,ht,block_forces a j c h i (List.mem_range.mp hi) 0 (by decide)] at he
    have he : (Clause.eval a ((clean c).map (lift old)) || Clause.eval a (added j c)) = true := by
      simpa only [Clause.eval,List.any_append] using hm
    rw [hn,Bool.or_false,rename_clause] at he
    simpa [clean,ht,dedup_eval] using he
  · exact taut_eval _ ht

theorem extend_new (a : Assignment) (j i v : ℕ) : extend a (fresh j i v) = false := by
  have h : (fresh j i v)%2 ≠ 0 := by unfold fresh; omega
  simp [extend,h]

theorem block_complete (a : Assignment) (j : ℕ) (c : Clause) (hC : c.length ≤ 3)
    (h : Clause.eval a c = true) : CNF.eval (extend a) (block j c) = true := by
  simp only [CNF.eval,List.all_eq_true,block,List.mem_append,List.mem_singleton,List.mem_flatMap]
  intro cl hc
  rcases hc with rfl | ⟨i,_,hc⟩
  · cases ht : taut c
    · have he : extend a ∘ old = a := funext (extend_old a)
      have h' := rename_clause (extend a) old (clean c)
      rw [he,show Clause.eval a (clean c) = true by simpa [clean,ht,dedup_eval] using h] at h'
      simp only [Clause.eval,List.any_append,show ((clean c).map (lift old)).any (Literal.eval (extend a)) = true from h',
        Bool.true_or]
    · apply List.any_eq_true.mpr
      refine ⟨(fresh j 0 0,false),List.mem_append_right _ ?_,by simp [Literal.eval,extend_new]⟩
      apply List.mem_map.mpr
      have hslot : 0 < 3-(clean c).length := by have h' := taut_space c hC ht; omega
      exact ⟨0,List.mem_range.mpr hslot,by simp [ht]⟩
  · exact List.all_eq_true.mp (placed_extend a j i) _ hc

theorem pad_sound (a : Assignment) (F : CNF) (j : ℕ) (h : CNF.eval a (padFrom j F) = true) :
    CNF.eval (a ∘ old) F = true := by
  induction F generalizing j with
  | nil => rfl
  | cons c F ih =>
    have he : CNF.eval a (block j c) = true ∧ CNF.eval a (padFrom (j+1) F) = true := by
      simpa only [padFrom,CNF.eval,List.all_append,Bool.and_eq_true_iff] using h
    exact Bool.and_eq_true_iff.mpr ⟨block_sound a j c he.1,ih (j+1) he.2⟩

theorem pad_complete (a : Assignment) (F : CNF) (hF : IsKCNF 3 F) (j : ℕ)
    (h : CNF.eval a F = true) : CNF.eval (extend a) (padFrom j F) = true := by
  induction F generalizing j with
  | nil => rfl
  | cons c F ih =>
    have he : Clause.eval a c = true ∧ CNF.eval a F = true := by
      simpa only [CNF.eval,List.all_cons,Bool.and_eq_true_iff] using h
    simpa only [padFrom,CNF.eval,List.all_append,Bool.and_eq_true_iff] using And.intro
      (block_complete a j c (hF c (List.mem_cons_self ..)) he.1)
      (ih (fun l hl => hF l (List.mem_cons_of_mem _ hl)) (j+1) he.2)

theorem pad_shape (F : CNF) (hF : IsKCNF 3 F) (j : ℕ) :
    ∀ c ∈ padFrom j F, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  induction F generalizing j with
  | nil => simp [padFrom]
  | cons c F ih =>
    intro cl hc
    rw [padFrom,List.mem_append] at hc
    rcases hc with h | h
    · exact block_shape j c (hF c (List.mem_cons_self ..)) cl h
    · exact ih (fun l hl => hF l (List.mem_cons_of_mem _ hl)) (j+1) cl h

theorem block_vars (j : ℕ) (c : Clause) (i : ℕ) :
    old i ∈ ids (block j c) ↔ i ∈ c.map Prod.fst := by
  have hAdded : old i ∉ (added j c).map Prod.fst := by
    intro h
    obtain ⟨l,hl,he⟩ := List.mem_map.mp h
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hl
    change fresh j p 0 = old i at he
    unfold fresh old at he
    omega
  have hPlaced : old i ∉ ids ((List.range (3-(clean c).length)).flatMap (placed j)) := by
    rw [ids_flatMap]
    intro hh
    obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hh
    rw [placed,ids_rename] at hp
    obtain ⟨v,_,he⟩ := List.mem_map.mp hp
    unfold fresh old at he
    omega
  rw [block,ids_append,List.mem_append]
  simp only [hPlaced,or_false]
  change old i ∈ (((clean c).map (lift old) ++ added j c).map Prod.fst ++ []) ↔ _
  rw [List.append_nil,List.map_append,List.mem_append,lifted_ids]
  simp only [hAdded,or_false]
  rw [← clean_vars c i]
  exact List.mem_map_of_injective old_inj

theorem pad_vars (F : CNF) (j i : ℕ) : old i ∈ ids (padFrom j F) ↔ i ∈ ids F := by
  induction F generalizing j with
  | nil => simp [padFrom,ids]
  | cons c F ih =>
    rw [padFrom,ids_append,List.mem_append,block_vars,ih]
    exact List.mem_append.symm

theorem block_fresh (a : Assignment) (j w : ℕ) (c : Clause) (ho : w % 2 = 1)
    (hw : w ∈ ids (block j c)) (h : CNF.eval a (block j c) = true) : a w = false := by
  rw [block,ids_append,List.mem_append] at hw
  rcases hw with hw | hw
  · change w ∈ ((clean c).map (lift old) ++ added j c).map Prod.fst ++ [] at hw
    rw [List.append_nil,List.map_append,List.mem_append,lifted_ids] at hw
    rcases hw with hw | hw
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hw
      simp [old] at ho
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hw
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
      exact block_forces a j c h i (List.mem_range.mp hi) 0 (by decide)
  · rw [ids_flatMap] at hw
    obtain ⟨i,hi,hw⟩ := List.mem_flatMap.mp hw
    rw [placed,ids_rename] at hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    have hvg : v < 7 := by
      change v ∈ gadget.flatMap (List.map Prod.fst) at hv
      obtain ⟨c,hc,hu⟩ := List.mem_flatMap.mp hv
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hu
      exact (shape c hc).2.2 _ hl
    exact block_forces a j c h i (List.mem_range.mp hi) v hvg

theorem pad_fresh (a : Assignment) (F : CNF) (j w : ℕ) (ho : w % 2 = 1)
    (hw : w ∈ ids (padFrom j F)) (h : CNF.eval a (padFrom j F) = true) : a w = false := by
  induction F generalizing j with
  | nil => simp [padFrom,ids] at hw
  | cons c F ih =>
    have he : CNF.eval a (block j c) = true ∧ CNF.eval a (padFrom (j+1) F) = true := by
      simpa only [padFrom,CNF.eval,List.all_append,Bool.and_eq_true_iff] using h
    rw [padFrom,ids_append,List.mem_append] at hw
    exact hw.elim (fun hc => block_fresh a j w c ho hc he.1) (fun hf => ih _ hf he.2)

end PEqualNP.Outside.UniqueTernaryGadget
