import PEqualNP.Outside.ExactRUPRefutationVerifier

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Search

/-- A polynomial bound on the encoded RUP trace gives a literal verifier
presentation in the reference definition of NP. -/
theorem BoundedRUPRefutationsInNP (q : Polynomial ℕ) :
    {x : List Bool | ∃ (φ ρ : CNF), encodeCNF φ = x ∧ (encodeCNF ρ).length ≤ q.eval x.length ∧
      IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map fun c => c.toFinset) ∧
      [] ∈ ρ} ∈ NP := by
  let R : Set (List Bool × List Bool) := {p | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
    IsRUPRun (clauseSet φ) (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ}
  refine ⟨R,q,ExactRUPRefutationVerifier.1,fun x => ?_⟩
  change (∃ φ ρ : CNF, encodeCNF φ = x ∧ (encodeCNF ρ).length ≤ q.eval x.length ∧
      IsRUPRun (clauseSet φ) (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ) ↔
    ∃ w : List Bool, w.length ≤ q.eval x.length ∧ (x,w) ∈ R
  constructor
  · rintro ⟨φ,ρ,hφ,hb,hr,he⟩
    exact ⟨encodeCNF ρ,hb,φ,ρ,hφ,rfl,hr,he⟩
  · rintro ⟨w,hb,φ,ρ,hφ,hw,hr,he⟩
    exact ⟨φ,ρ,hφ,hw.symm ▸ hb,hr,he⟩

end PEqualNP.Outside
