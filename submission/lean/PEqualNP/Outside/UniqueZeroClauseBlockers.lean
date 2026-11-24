import PEqualNP.Defs

namespace PEqualNP.Outside.ZeroClauseBlockers
open PEqualNP.Search

def assign {n : ℕ} (b : Fin n → Bool) : Assignment :=
  fun i => if h : i < n then b ⟨i,h⟩ else false

theorem failed_clause (F : CNF) (a : Assignment) (h : CNF.eval a F = false) :
    ∃ c ∈ F, Clause.eval a c = false := by
  by_contra hn
  push Not at hn
  have ht : CNF.eval a F = true := List.all_eq_true.mpr (fun c hc => by simpa using hn c hc)
  rw [ht] at h
  cases h

theorem rejects_literal {c : Clause} {a : Assignment} (h : Clause.eval a c = false)
    {l : Literal} (hl : l ∈ c) : Literal.eval a l = false := by
  cases he : Literal.eval a l
  · rfl
  · have ht : Clause.eval a c = true := List.any_eq_true.mpr ⟨l,hl,he⟩
    rw [ht] at h
    cases h

theorem singleton (F : CNF) (n : ℕ) (i : Fin n)
    (hZero : CNF.eval (fun _ => false) F = true)
    (hUnique : ∀ b : Fin n → Bool, CNF.eval (assign b) F = true → ∀ j, b j = false) :
    ∃ c ∈ F, (i.1,false) ∈ c ∧ ∀ l ∈ c, l.2 = false → l.1 = i.1 := by
  let b : Fin n → Bool := fun j => decide (j = i)
  have hF : CNF.eval (assign b) F = false := by
    cases h : CNF.eval (assign b) F
    · rfl
    · have hf := hUnique b h i
      simp [b] at hf
  obtain ⟨c,hc,hFail⟩ := failed_clause F _ hF
  have hh : ∀ l ∈ c, l.2 = false → l.1 = i.1 := by
    intro l hl hSign
    have hLit := rejects_literal hFail hl
    by_contra hn
    have hv : assign b l.1 = false := by
      unfold assign
      split
      · next h =>
        have he : (⟨l.1,h⟩ : Fin n) ≠ i := fun e => hn (congrArg Fin.val e)
        simp [b,he]
      · rfl
    simp [Literal.eval,hSign,hv] at hLit
  have hc0 : Clause.eval (fun _ => false) c = true := List.all_eq_true.mp hZero c hc
  obtain ⟨l,hl,hLit⟩ := List.any_eq_true.mp hc0
  have hs : l.2 = false := by cases h : l.2 <;> simp [Literal.eval,h] at hLit ⊢
  refine ⟨c,hc,?_,hh⟩
  obtain ⟨name,sign⟩ := l
  have he := hh (name,sign) hl hs
  cases hs
  rw [← he]
  exact hl

theorem all_negative (F : CNF) (n : ℕ) (hn : 0 < n)
    (hNames : ∀ c ∈ F, ∀ l ∈ c, l.1 < n)
    (hUnique : ∀ b : Fin n → Bool, CNF.eval (assign b) F = true → ∀ j, b j = false) :
    ∃ c ∈ F, ∀ l ∈ c, l.2 = false := by
  let b : Fin n → Bool := fun _ => true
  have hF : CNF.eval (assign b) F = false := by
    cases h : CNF.eval (assign b) F
    · rfl
    · exact hUnique b h ⟨0,hn⟩
  obtain ⟨c,hc,hFail⟩ := failed_clause F _ hF
  refine ⟨c,hc,fun l hl => ?_⟩
  have he := rejects_literal hFail hl
  simpa [Literal.eval,assign,b,hNames c hc l hl] using he

end PEqualNP.Outside.ZeroClauseBlockers

open PEqualNP.Search

theorem PEqualNP.Outside.UniqueZeroClauseBlockers :
    ∀ (F : CNF) (n : ℕ), 0 < n →
      (∀ c ∈ F, ∀ l ∈ c, l.1 < n) →
      CNF.eval (fun _ => false) F = true →
      (∀ a : Fin n → Bool,
        CNF.eval (fun i => if h : i < n then a ⟨i,h⟩ else false) F = true → ∀ j, a j = false) →
      (∀ i < n, ∃ c ∈ F, (i,false) ∈ c ∧ ∀ l ∈ c, l.2 = false → l.1 = i) ∧
      (∃ c ∈ F, ∀ l ∈ c, l.2 = false) := by
  intro F n hn hNames hZero hUnique
  open PEqualNP.Outside.ZeroClauseBlockers in
  exact ⟨fun i hi => singleton F n ⟨i,hi⟩ hZero hUnique,all_negative F n hn hNames hUnique⟩
