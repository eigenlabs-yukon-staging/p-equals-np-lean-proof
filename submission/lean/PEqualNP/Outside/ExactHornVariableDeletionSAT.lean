import PEqualNP.Outside.ExactVariableDeletionSAT
import PEqualNP.Outside.ExactHornSAT
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

/-- Exact canonical recognition and SAT after deleting occurrences of a fixed
number of variables so the structural formula becomes Horn. -/
theorem ExactHornVariableDeletionSAT (k : ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ xs : List ℕ, xs.length ≤ k ∧ ∀ c ∈ φ,
        (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1} ∈ P ∧
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ xs : List ℕ, xs.length ≤ k ∧ ∀ c ∈ φ,
        (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1) ∧
      Satisfiable φ} ∈ P := by
  let G : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1}
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    (∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧ Satisfiable φ}
  have hg (φ : CNF) : encodeCNF φ ∈ G ↔ ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1 := by
    constructor
    · rintro ⟨f,he,h⟩
      exact encodeCNF_injective he ▸ h
    · exact fun h => ⟨φ,rfl,h⟩
  have hsub (φ ψ : CNF) (h : ψ.Sublist φ) (he : encodeCNF φ ∈ G) : encodeCNF ψ ∈ G :=
    (hg ψ).mpr (fun c hc => (hg φ).mp he c (h.subset hc))
  have hd (φ : CNF) (h : encodeCNF φ ∈ G) : encodeCNF φ ∈ D ↔ Satisfiable φ := by
    constructor
    · rintro ⟨f,he,_,hs⟩
      exact encodeCNF_injective he ▸ hs
    · exact fun hs => ⟨φ,rfl,(hg φ).mp h,hs⟩
  have hf (xs : List ℕ) (φ : CNF) :
      encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G ↔
      ∀ c ∈ φ, (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1 := by
    rw [hg]
    constructor
    · intro h c hc
      have he := h _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
      simpa [List.filter_filter,Bool.and_comm] using he
    · intro h c hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      simpa [List.filter_filter,Bool.and_comm] using h d hd
  simpa only [hf] using ExactVariableDeletionSAT G D MeasuredHornGuard ExactHornSAT hsub hd k

end PEqualNP.Outside
