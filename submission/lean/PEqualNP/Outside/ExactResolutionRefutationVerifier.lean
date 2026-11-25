import PEqualNP.Outside.MeasuredResolutionDerivation
import PEqualNP.Outside.MeasuredCanonicalTraceWithEmptyClause
import PEqualNP.ProofComplexity.Helpers.Resolution

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Search

private theorem trace_empty (ρ : CNF) : [] ∈ ρ ↔ (∅ : FinClause) ∈ ρ.map List.toFinset := by
  constructor
  · exact fun h => List.mem_map.mpr ⟨[],h,List.toFinset_nil⟩
  · intro h
    obtain ⟨c,hc,hn⟩ := List.mem_map.mp h
    cases c with
    | nil => exact hc
    | cons l ls =>
        have hm : l ∈ (l :: ls).toFinset := List.mem_toFinset.mpr List.mem_cons_self
        rw [hn] at hm
        simp at hm

private theorem valid_refutation (φ ρ : CNF) :
    (PEqualNP.ProofComplexity.IsDerivation (clauseSet φ) (ρ.map List.toFinset) ∧ [] ∈ ρ) ↔
    PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset) := by
  exact and_congr_right (fun _ => trace_empty ρ)

/-- Exact raw verification of newest-first resolution refutations, with
a proof that a verified trace implies unsatisfiability of its input. -/
theorem ExactResolutionRefutationVerifier :
    DecidableInPolyTime encodePair
      {p : List Bool × List Bool | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
        PEqualNP.ProofComplexity.IsRefutation
          {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset)} ∧
    (∀ (φ ρ : CNF), PEqualNP.ProofComplexity.IsRefutation
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) → ¬ Satisfiable φ) := by
  constructor
  · obtain ⟨test,ht,hs⟩ := MeasuredResolutionDerivation
    have h := MeasuredCanonicalTraceWithEmptyClause
      (fun φ ρ => PEqualNP.ProofComplexity.IsDerivation (clauseSet φ) (ρ.map List.toFinset)) test ht hs
    have he :
        {p : List Bool × List Bool | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
          PEqualNP.ProofComplexity.IsDerivation (clauseSet φ) (ρ.map List.toFinset) ∧ [] ∈ ρ} =
        {p : List Bool × List Bool | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
          PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset)} := by
      ext p
      exact exists_congr (fun φ => exists_congr (fun ρ =>
        and_congr_right (fun _ => and_congr_right (fun _ => valid_refutation φ ρ))))
    rw [he] at h
    exact h
  · intro φ ρ hr
    rintro ⟨σ,hσ⟩
    have hF : PEqualNP.ProofComplexity.Satisfies σ (clauseSet φ) := by
      rintro c ⟨d,hd,rfl⟩
      obtain ⟨l,hl,he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hσ d hd)
      exact ⟨l,List.mem_toFinset.mpr hl,by simpa [Literal.eval] using he⟩
    have ha := PEqualNP.ProofComplexity.Helpers.derivation_sound σ hr.1 hF ∅ hr.2
    obtain ⟨l,hl,_⟩ := ha
    simp at hl

end PEqualNP.Outside
