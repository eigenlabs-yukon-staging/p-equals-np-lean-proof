import PEqualNP.Outside.ExactPackedProductBudgetSAT
import PEqualNP.Outside.ExactRenamableHornGuard
import PEqualNP.Outside.ExactRenamableHornSAT
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Search

private def renamable (φ : CNF) : Prop :=
  ∃ flip : Assignment, ∀ c ∈ φ,
    ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1

private theorem extend_renamable (base units : CNF) (hb : renamable base) (hu : IsKCNF 1 units) :
    renamable (base ++ units) := by
  obtain ⟨flip,h⟩ := hb
  refine ⟨flip,fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc
  · exact (List.length_filter_le _ _).trans (by simpa using hu c hc)

/-- Product-budget branching with a separately supplied renamable Horn base. -/
theorem ExactPackedRenamableHornProductSAT (q : Polynomial ℕ) :
    {x : List Bool | ∃ (base extra : CNF),
      List.replicate (encodeCNF base).length true ++ false :: (encodeCNF base ++ encodeCNF extra) = x ∧
      (∃ flip : Assignment, ∀ c ∈ base,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1) ∧
      (extra.map List.length).prod ≤ q.eval x.length ∧ Satisfiable (base ++ extra)} ∈ P := by
  let G : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ renamable φ}
  let B : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ renamable φ ∧ Satisfiable φ}
  have hG : G ∈ P := ExactRenamableHornGuard
  have hB : B ∈ P := ExactRenamableHornSAT
  have hguard (base : CNF) : encodeCNF base ∈ G ↔ renamable base := by
    constructor
    · rintro ⟨φ,he,hr⟩
      exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective he) ▸ hr
    · intro hr
      exact ⟨base,rfl,hr⟩
  have hroute (base : CNF) (hb : encodeCNF base ∈ G) (units : CNF) (hu : IsKCNF 1 units) :
      encodeCNF (base ++ units) ∈ B ↔ Satisfiable (base ++ units) := by
    constructor
    · rintro ⟨F,he,_,hf⟩
      exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective he) ▸ hf
    · intro hsat
      exact ⟨base ++ units,rfl,extend_renamable base units ((hguard base).mp hb) hu,hsat⟩
  have h := ExactPackedProductBudgetSAT G B hG hB hroute q
  simp only [hguard] at h
  exact h

end PEqualNP.Outside
