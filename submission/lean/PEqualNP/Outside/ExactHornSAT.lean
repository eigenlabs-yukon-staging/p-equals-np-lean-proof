import PEqualNP.Outside.MeasuredHornSAT
import PEqualNP.Outside.MeasuredHornGuard
import PEqualNP.Library.L046

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Search

/-- The exact language of satisfiable canonical Horn CNF encodings is in the reference P. -/
theorem ExactHornSAT :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧ Satisfiable φ} ∈ P := by
  obtain ⟨D, hD, hspec⟩ := MeasuredHornSAT
  let G : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1}
  have h : G ⊓ D ∈ P := L046 G D MeasuredHornGuard hD
  have he : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧ Satisfiable φ} = G ⊓ D := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧ Satisfiable φ) ↔
      (∃ φ : CNF, encodeCNF φ = x ∧ ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧ x ∈ D
    constructor
    · rintro ⟨φ,rfl,hφ,hs⟩
      exact ⟨⟨φ,rfl,hφ⟩,(hspec φ hφ).mpr hs⟩
    · rintro ⟨⟨φ,rfl,hφ⟩,hd⟩
      exact ⟨φ,rfl,hφ,(hspec φ hφ).mp hd⟩
  rwa [he]

end PEqualNP.Outside
