import PEqualNP.Defs
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Search

def taut (c : Clause) : Bool := c.any (fun l => decide ((l.1,!l.2) ∈ c))

def normalize (F : CNF) : CNF :=
  F.filterMap (fun c => if taut c then none else some c.dedup)

theorem taut_iff (c : Clause) :
    taut c = true ↔ ∃ i, (i,true) ∈ c ∧ (i,false) ∈ c := by
  simp only [taut,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,b⟩,h1,h2⟩
    cases b
    · exact ⟨i,h2,h1⟩
    · exact ⟨i,h1,h2⟩
  · rintro ⟨i,h1,h2⟩
    exact ⟨(i,true),h1,h2⟩

theorem taut_eval (σ : Assignment) {c : Clause} (h : taut c = true) :
    Clause.eval σ c = true := by
  obtain ⟨i,h1,h2⟩ := (taut_iff c).mp h
  apply List.any_eq_true.mpr
  cases hb : σ i
  · exact ⟨(i,false),h2,by simp [Literal.eval,hb]⟩
  · exact ⟨(i,true),h1,by simp [Literal.eval,hb]⟩

theorem dedup_eval (σ : Assignment) (c : Clause) : Clause.eval σ c.dedup = Clause.eval σ c := by
  apply Bool.eq_iff_iff.mpr
  simp only [Clause.eval,List.any_eq_true,List.mem_dedup]

theorem normalize_eval (σ : Assignment) (F : CNF) : CNF.eval σ (normalize F) = CNF.eval σ F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    cases h : taut c
    · have hcons : normalize (c::F) = c.dedup :: normalize F := by
        simp only [normalize,List.filterMap_cons,h,Bool.false_eq_true,ite_false]
      rw [hcons]
      change (Clause.eval σ c.dedup && CNF.eval σ (normalize F)) =
        (Clause.eval σ c && CNF.eval σ F)
      rw [dedup_eval,ih]
    · have hcons : normalize (c::F) = normalize F := by
        simp only [normalize,List.filterMap_cons,h,ite_true]
      rw [hcons,ih]
      change CNF.eval σ F = (Clause.eval σ c && CNF.eval σ F)
      rw [taut_eval σ h,Bool.true_and]

theorem normalize_sublist (F : CNF) : List.Sublist (normalize F).flatten F.flatten := by
  induction F with
  | nil => simp [normalize]
  | cons c F ih =>
    cases h : taut c
    · simp only [normalize,List.filterMap_cons,h,Bool.false_eq_true,ite_false,List.flatten_cons] at *
      exact (List.dedup_sublist c).append ih
    · simp only [normalize,List.filterMap_cons,h,ite_true,List.flatten_cons]
      simpa only [normalize,List.nil_append] using (List.nil_sublist c).append ih

theorem normalized_nodup {c : Clause} (h : taut c = false) : (c.dedup.map Prod.fst).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_dedup c)
  rintro ⟨i,a⟩ hi ⟨j,b⟩ hj he
  have h₁ := List.mem_dedup.mp hi
  have h₂ := List.mem_dedup.mp hj
  change i = j at he
  subst j
  cases a <;> cases b
  · rfl
  · exact False.elim (Bool.noConfusion (h.symm.trans ((taut_iff c).mpr ⟨i,h₂,h₁⟩)))
  · exact False.elim (Bool.noConfusion (h.symm.trans ((taut_iff c).mpr ⟨i,h₁,h₂⟩)))
  · rfl

theorem normalize_shape (F : CNF) (h : IsKCNF 3 F) (c : Clause) (hc : c ∈ normalize F) :
    c.length ≤ 3 ∧ (c.map Prod.fst).Nodup := by
  obtain ⟨q,hq,hc⟩ := List.mem_filterMap.mp hc
  cases ht : taut q
  · have he : q.dedup = c := by simpa [ht] using hc
    subst c
    exact ⟨(List.dedup_sublist q).length_le.trans (h _ hq),normalized_nodup ht⟩
  · simp [ht] at hc

end PEqualNP.Outside.TernaryGadget
