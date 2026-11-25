import PEqualNP.Outside.ExactResolutionRefutationVerifier

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Search

/-- A polynomial bound on the encoded resolution trace gives a literal verifier
presentation in the reference definition of NP. -/
theorem BoundedResolutionRefutationsInNP (q : Polynomial ℕ) :
    {x : List Bool | ∃ (φ ρ : CNF), encodeCNF φ = x ∧ (encodeCNF ρ).length ≤ q.eval x.length ∧
      PEqualNP.ProofComplexity.IsRefutation {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset)} ∈ NP := by
  let R : Set (List Bool × List Bool) := {p | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
    PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset)}
  refine ⟨R,q,ExactResolutionRefutationVerifier.1,fun x => ?_⟩
  change (∃ φ ρ : CNF, encodeCNF φ = x ∧ (encodeCNF ρ).length ≤ q.eval x.length ∧
      PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset)) ↔
    ∃ w : List Bool, w.length ≤ q.eval x.length ∧ (x,w) ∈ R
  constructor
  · rintro ⟨φ,ρ,hφ,hb,hr⟩
    exact ⟨encodeCNF ρ,hb,φ,ρ,hφ,rfl,hr⟩
  · rintro ⟨w,hb,φ,ρ,hφ,hw,hr⟩
    exact ⟨φ,ρ,hφ,hw.symm ▸ hb,hr⟩

end PEqualNP.Outside
