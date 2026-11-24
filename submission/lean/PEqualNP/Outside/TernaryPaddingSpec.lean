import PEqualNP.Outside.TernaryPaddingRaw

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Search
open PEqualNP.Outside.CNFWidth (Word evenLit evenLit_enc)
open PEqualNP.Library.Universal (sel)

def slots (c : Clause) (n : ℕ) : Word := (c[n]?).elim [] encodeLiteral

theorem slots_words (c : Clause) (h : c.length ≤ 3) :
    optional (slots c 0) ++ optional (slots c 1) ++ optional (slots c 2) =
      c.map encodeLiteral := by
  rcases c with _ | ⟨l,_ | ⟨r,_ | ⟨s,cs⟩⟩⟩
  all_goals simp only [slots,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
    Option.elim,optional_lit,List.map_cons,List.map_nil]
  · rfl
  · rfl
  · rfl
  · have hc : cs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
    subst cs
    rfl

private theorem append_ne_nil (a b : Word) : a ++ b ≠ [] ↔ a ≠ [] ∨ b ≠ [] := by
  change (¬ a ++ b = []) ↔ (¬ a = []) ∨ (¬ b = [])
  rw [List.append_eq_nil_iff]
  tauto

private theorem conflict_empty : conflict [] [] = [] := rfl

theorem slots_taut (c : Clause) (h : c.length ≤ 3) :
    (conflict (slots c 0) (slots c 1) ++ conflict (slots c 0) (slots c 2) ++
      conflict (slots c 1) (slots c 2) ≠ []) ↔ taut c = true := by
  rcases c with _ | ⟨⟨i,a⟩,_ | ⟨⟨j,b⟩,_ | ⟨⟨k,d⟩,cs⟩⟩⟩
  · decide
  · cases a <;>
      simp [slots,taut,conflict_nil_right _ (lit_tail_nonempty _),conflict_empty]
  · cases a <;> cases b <;>
      simp only [slots,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
        Option.elim,append_ne_nil,conflict_cons,
        conflict_nil_right _ (lit_tail_nonempty _),not_true_eq_false,not_false_eq_true,or_false,and_false,and_true,false_or,false_and,true_and,taut_iff,
        List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] <;>
      grind
  · have hc : cs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
    subst cs
    cases a <;> cases b <;> cases d <;>
      simp only [slots,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.elim,append_ne_nil,conflict_cons,taut_iff,
        List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] <;>
      grind


theorem carry_slots (c : Clause) (j : ℕ) (h : c.length ≤ 3) :
    carry (12*j).bits (slots c 0) (slots c 1) (slots c 2) = encodeCNF (block j c.dedup) := by
  rw [carry_eq,slots_words c h]
  rw [List.dedup_map_of_injective
    PEqualNP.Library.SearchHelpers.TwoSat.encodeLiteral_injective]
  simp only [List.length_map,List.flatMap_map,Function.comp_def,evenLit_enc,Bool.false_eq_true,if_false]
  rw [localWord_enc,local_tail (3-c.dedup.length) j c.dedup rfl]
  simp [block,encodeCNF,encodeClause,List.flatMap_append,List.flatMap_map,Function.comp_def,lift,old,
    List.append_assoc]

theorem emit_slots (c : Clause) (j : ℕ) (h : c.length ≤ 3) :
    emitRaw (12*j).bits (slots c 0) (slots c 1) (slots c 2) =
      if taut c then [] else encodeCNF (block j c.dedup) := by
  have hh := slots_taut c h
  unfold emitRaw sel
  split
  · next he =>
    have hc : taut c ≠ true := fun ht => (hh.mpr ht) he
    simp [hc,carry_slots c j h]
  · next he => simp [hh.mp he]

end PEqualNP.Outside.TernaryGadget
