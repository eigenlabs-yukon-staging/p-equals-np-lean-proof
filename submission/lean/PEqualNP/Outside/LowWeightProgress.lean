import PEqualNP.Library.SearchHelpers.Weight

namespace PEqualNP.Outside
open PEqualNP.Search PEqualNP.Library.SearchHelpers

theorem lowWeight_has_first_literal (c : Clause) (φ : CNF) (h : wt (c :: φ) < 1) : c ≠ [] := by
  intro hc
  rw [hc,wt_cons] at h
  have hn := wt_nonneg φ
  norm_num at h
  linarith

theorem lowWeight_restrict (φ : CNF) (x : ℕ)
    (hd : ∀ c ∈ φ, (c.map Prod.fst).Nodup) (hw : wt φ < 1) :
    (∀ b, ∀ c ∈ restrict x b φ, (c.map Prod.fst).Nodup) ∧
    wt (restrict x (decide (wt (restrict x true φ) < 1)) φ) < 1 := by
  constructor
  · intro b c hc
    simp only [restrict,List.mem_map,List.mem_filter] at hc
    obtain ⟨c₀,⟨hm,_⟩,rfl⟩ := hc
    exact (hd c₀ hm).sublist (List.filter_sublist.map _)
  · have h := wt_restrict_le x φ hd
    by_cases ht : wt (restrict x true φ) < 1
    · simpa only [ht,decide_true] using ht
    · simp only [ht,decide_false]
      linarith

theorem restrict_eval_update (φ : CNF) (x : ℕ) (b : Bool) (σ : ℕ → Bool)
    (h : CNF.eval σ (restrict x b φ) = true) :
    CNF.eval (Function.update σ x b) φ = true := by
  simp only [CNF.eval,List.all_eq_true] at h ⊢
  intro c hc
  simp only [Clause.eval,List.any_eq_true,Literal.eval,beq_iff_eq] at h ⊢
  by_cases hb : (x,b) ∈ c
  · exact ⟨(x,b),hb,by simp⟩
  · have hm : (c.filter fun l => decide (l.1 ≠ x)) ∈ restrict x b φ := by
      simp only [restrict,List.mem_map,List.mem_filter]
      exact ⟨c,⟨hc,by simpa using hb⟩,rfl⟩
    obtain ⟨l,hl,he⟩ := h _ hm
    simp only [List.mem_filter,decide_eq_true_eq] at hl
    exact ⟨l,hl.1,by rw [Function.update_of_ne hl.2]; exact he⟩

private theorem clause_encoding_monotone {c d : Clause} (h : c.Sublist d) :
    (encodeClause c).length ≤ (encodeClause d).length := by
  simp only [encodeClause,List.length_append]
  exact Nat.add_le_add_right (h.flatMap encodeLiteral).length_le _

private theorem clause_encoding_strict {c d : Clause} (h : c.Sublist d) (hnt : c ≠ d) :
    (encodeClause c).length < (encodeClause d).length := by
  induction h with
  | slnil => contradiction
  | cons l h ih =>
      have hm := clause_encoding_monotone h
      have hl : 0 < (encodeLiteral l).length := by simp [encodeLiteral]
      simp only [encodeClause,List.flatMap_cons,List.length_append] at hm ⊢
      omega
  | cons_cons l h ih =>
      have hn := ih (fun he => hnt (congrArg (List.cons l) he))
      simp only [encodeClause,List.flatMap_cons,List.length_append] at hn ⊢
      omega

private theorem encoded_cons_length (c : Clause) (φ : CNF) :
    (encodeCNF (c :: φ)).length = (encodeClause c).length + (encodeCNF φ).length := by
  simp [encodeCNF]

theorem restrict_encoding_le (x : ℕ) (b : Bool) (φ : CNF) :
    (encodeCNF (restrict x b φ)).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [encoded_cons_length]
      by_cases h : (x,b) ∈ c
      · change (encodeCNF ((List.filter _ (c :: φ)).map _)).length ≤ _
        simp only [List.filter_cons,h,decide_false,ite_false]
        exact ih.trans (Nat.le_add_left _ _)
      · have hm := clause_encoding_monotone (List.filter_sublist (l := c) (p := fun l => decide (l.1 ≠ x)))
        change (encodeCNF ((List.filter _ (c :: φ)).map _)).length ≤ _
        simp only [List.filter_cons,h,not_false_eq_true,decide_true,ite_true,List.map_cons,encoded_cons_length]
        exact Nat.add_le_add hm ih

theorem restrict_encoding_lt (l : Literal) (c : Clause) (φ : CNF) (b : Bool) :
    (encodeCNF (restrict l.1 b ((l :: c) :: φ))).length <
      (encodeCNF ((l :: c) :: φ)).length := by
  rw [encoded_cons_length]
  have ht := restrict_encoding_le l.1 b φ
  by_cases h : (l.1,b) ∈ l :: c
  · change (encodeCNF ((List.filter _ ((l :: c) :: φ)).map _)).length < _
    simp only [List.filter_cons,h,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
    change (encodeCNF (restrict l.1 b φ)).length < _
    have hp : 0 < (encodeClause (l :: c)).length := by simp [encodeClause]
    omega
  · let pred := fun z : Literal => decide (z.1 ≠ l.1)
    have hsub : ((l :: c).filter pred).Sublist (l :: c) := List.filter_sublist
    have hn : (l :: c).filter pred ≠ l :: c := by
      intro he
      have hm : l ∈ (l :: c).filter pred := he.symm ▸ List.mem_cons_self
      simpa [pred] using hm
    have hm := clause_encoding_strict hsub hn
    change (encodeCNF ((List.filter _ ((l :: c) :: φ)).map _)).length < _
    simp only [List.filter_cons,h,not_false_eq_true,decide_true,ite_true,List.map_cons,encoded_cons_length]
    exact Nat.add_lt_add_of_lt_of_le (by simpa [pred] using hm) ht

end PEqualNP.Outside
