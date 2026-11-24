import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.RestrictCnfHelpers

open PEqualNP.Search

/-- A satisfied clause is dropped. Otherwise only unassigned literals remain. -/
def restrict (ρ : ℕ → Option Bool) (φ : CNF) : CNF :=
  φ.filterMap fun c =>
    if c.any (fun l => ρ l.1 == some l.2) then none
    else some (c.filter (fun l => (ρ l.1).isNone))

def merged (ρ : ℕ → Option Bool) (σ : Assignment) : Assignment :=
  fun i => (ρ i).getD (σ i)

theorem clause_kept_eval (ρ : ℕ → Option Bool) (σ : Assignment) (c : Clause)
    (h : c.any (fun l => ρ l.1 == some l.2) = false) :
    Clause.eval σ (c.filter fun l => (ρ l.1).isNone) = Clause.eval (merged ρ σ) c := by
  apply Bool.eq_iff_iff.mpr
  simp only [Clause.eval, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨l, ⟨hl, hs⟩, hv⟩
    exact ⟨l, hl, by simpa [Literal.eval, merged, Option.isNone_iff_eq_none.mp hs] using hv⟩
  · rintro ⟨l, hl, hv⟩
    cases he : ρ l.1 with
    | none =>
      exact ⟨l, ⟨hl, by simp [he]⟩, by simpa [Literal.eval, merged, he] using hv⟩
    | some b =>
      have hb : b = l.2 := by simpa [Literal.eval, merged, he] using hv
      have hf : c.any (fun l => ρ l.1 == some l.2) = true :=
        List.any_eq_true.mpr ⟨l, hl, by simp [he, hb]⟩
      rw [h] at hf
      cases hf

theorem eval_restrict (ρ : ℕ → Option Bool) (σ : Assignment) (φ : CNF) :
    CNF.eval σ (restrict ρ φ) = CNF.eval (merged ρ σ) φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    cases h : c.any (fun l => ρ l.1 == some l.2)
    · simp only [restrict, List.filterMap_cons, h, Bool.false_eq_true, ite_false, CNF.eval,
        List.all_cons] at ih ⊢
      rw [clause_kept_eval ρ σ c h, ih]
    · obtain ⟨l, hl, hv⟩ := List.any_eq_true.mp h
      have he : ρ l.1 = some l.2 := by simpa using hv
      have hs : Clause.eval (merged ρ σ) c = true :=
        List.any_eq_true.mpr ⟨l, hl, by simp [Literal.eval, merged, he]⟩
      simp only [restrict, List.filterMap_cons, h, ite_true, CNF.eval, List.all_cons,
        hs, Bool.true_and] at ih ⊢
      exact ih

theorem sat_restrict_iff (ρ : ℕ → Option Bool) (φ : CNF) :
    Satisfiable (restrict ρ φ) ↔
      ∃ σ : Assignment, CNF.eval σ φ = true ∧ ∀ i b, ρ i = some b → σ i = b := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨merged ρ σ, (eval_restrict ρ σ φ).symm ▸ hσ, ?_⟩
    intro i b hi
    simp [merged, hi]
  · rintro ⟨σ, hσ, hρ⟩
    refine ⟨σ, ?_⟩
    rw [eval_restrict]
    have e : merged ρ σ = σ := by
      funext i
      cases he : ρ i with
      | none => simp [merged, he]
      | some b => simpa [merged, he] using (hρ i b he).symm
    rwa [e]

theorem restrict_width {ρ : ℕ → Option Bool} {φ : CNF} {k : ℕ}
    (h : ∀ c ∈ φ, (c.filter (fun l => (ρ l.1).isNone)).length ≤ k) :
    IsKCNF k (restrict ρ φ) := by
  intro c hc
  obtain ⟨c', hc', hw⟩ := List.mem_filterMap.mp hc
  cases hb : c'.any (fun l => ρ l.1 == some l.2)
  · simp [hb] at hw
    subst c
    exact h c' hc'
  · simp [hb] at hw

end PEqualNP.Outside.RestrictCnfHelpers
