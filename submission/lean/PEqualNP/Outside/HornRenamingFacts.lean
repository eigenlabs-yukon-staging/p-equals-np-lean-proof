import PEqualNP.Defs.Search
import Mathlib.Data.List.Basic

namespace PEqualNP.Outside.HornRenamingFacts

open PEqualNP.Search

def renameClause (ρ : Assignment) (c : Clause) : Clause :=
  c.map fun l => (l.1, xor l.2 (ρ l.1))

def rename (ρ : Assignment) (φ : CNF) : CNF := φ.map (renameClause ρ)

def pairClauses : Clause → CNF
  | [] => []
  | l :: c => c.map (fun d => [l, d]) ++ pairClauses c

def pairCNF (φ : CNF) : CNF := φ.flatMap pairClauses

theorem rename_eval (ρ σ : Assignment) (φ : CNF) :
    CNF.eval σ (rename ρ φ) = CNF.eval (fun i => xor (σ i) (ρ i)) φ := by
  have h (l : Literal) :
      Literal.eval σ (l.1, xor l.2 (ρ l.1)) =
        Literal.eval (fun i => xor (σ i) (ρ i)) l := by
    unfold Literal.eval
    dsimp only
    cases h₁ : l.2 <;> cases h₂ : σ l.1 <;> cases h₃ : ρ l.1 <;> simp [h₁, h₂, h₃]
  simp [rename, renameClause, CNF.eval, Clause.eval, List.all_map, List.any_map, Function.comp_def, h] <;> rfl

theorem sat_rename (ρ : Assignment) (φ : CNF) :
    Satisfiable (rename ρ φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨fun i => xor (σ i) (ρ i), (rename_eval ρ σ φ).symm ▸ h⟩
  · rintro ⟨σ, hs⟩
    let s : Assignment := fun i => xor (σ i) (ρ i)
    have he : (fun i => xor (s i) (ρ i)) = σ := by
      funext i
      unfold s
      cases σ i <;> cases ρ i <;> rfl
    exact ⟨s, by rwa [rename_eval, he]⟩

private theorem sign_eq (ρ : Assignment) (l : Literal) :
    xor l.2 (ρ l.1) = !Literal.eval ρ l := by
  unfold Literal.eval
  cases l.2 <;> cases ρ l.1 <;> rfl

theorem pairClauses_correct (ρ : Assignment) (c : Clause) :
    CNF.eval ρ (pairClauses c) = true ↔ ((renameClause ρ c).filter Prod.snd).length ≤ 1 := by
  induction c with
  | nil => simp [pairClauses, renameClause, CNF.eval]
  | cons l c ih =>
    have all_correct : (∀ d ∈ c, Literal.eval ρ d = true) ↔
        ((renameClause ρ c).filter Prod.snd).length = 0 := by
      simp only [renameClause, List.filter_map, List.length_map, List.length_eq_zero_iff,
        List.filter_eq_nil_iff, Function.comp_def, sign_eq, Bool.not_eq_true]
      constructor
      · intro ha d hd
        simpa [ha d hd]
      · intro ha d hd
        simpa using ha d hd
    have hallpair : CNF.eval ρ (c.map (fun d => [l, d])) = true ↔
        Literal.eval ρ l = true ∨ ∀ d ∈ c, Literal.eval ρ d = true := by
      simp only [CNF.eval, List.all_map, Function.comp_def, Clause.eval, List.any_cons,
        List.any_nil, Bool.or_false, List.all_eq_true, Bool.or_eq_true]
      by_cases hl : Literal.eval ρ l = true <;> simp [hl]
    change (c.map (fun d => [l, d]) ++ pairClauses c).all (Clause.eval ρ) = true ↔ _
    rw [List.all_append, Bool.and_eq_true]
    change (CNF.eval ρ (c.map (fun d => [l, d])) = true ∧ CNF.eval ρ (pairClauses c) = true) ↔ _
    rw [hallpair, all_correct, ih]
    simp only [renameClause, List.map_cons, List.filter_cons, sign_eq]
    cases h : Literal.eval ρ l
    · simp only [Bool.false_eq_true, false_or, Bool.not_false, ite_true, List.length_cons]
      omega
    · simp

theorem pairCNF_correct (ρ : Assignment) (φ : CNF) :
    CNF.eval ρ (pairCNF φ) = true ↔ ∀ c ∈ rename ρ φ, (c.filter Prod.snd).length ≤ 1 := by
  induction φ with
  | nil => simp [pairCNF, rename, CNF.eval]
  | cons c cs ih =>
    change (pairClauses c ++ pairCNF cs).all (Clause.eval ρ) = true ↔
      ∀ d ∈ renameClause ρ c :: rename ρ cs, (d.filter Prod.snd).length ≤ 1
    rw [List.all_append, Bool.and_eq_true]
    change (CNF.eval ρ (pairClauses c) = true ∧ CNF.eval ρ (pairCNF cs) = true) ↔ _
    rw [pairClauses_correct, ih]
    simp

theorem pairCNF_two (φ : CNF) : IsKCNF 2 (pairCNF φ) := by
  intro c h
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp h
  clear h hd
  induction d with
  | nil => simp [pairClauses] at hc
  | cons l d ih =>
    simp only [pairClauses, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨r, _, rfl⟩ | hc
    · simp
    · exact ih hc

end PEqualNP.Outside.HornRenamingFacts
