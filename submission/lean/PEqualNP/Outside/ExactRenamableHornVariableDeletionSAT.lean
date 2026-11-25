import PEqualNP.Outside.ExactVariableDeletionSAT
import PEqualNP.Outside.ExactRenamableHornSAT
import PEqualNP.Outside.ExactRenamableHornGuard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

/-- Exact recognition and satisfiability for CNFs that become renamable Horn
after erasing the occurrences of at most a fixed number of variables. -/
theorem ExactRenamableHornVariableDeletionSAT (k : ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ xs : List ℕ, xs.length ≤ k ∧ ∃ flip : Assignment, ∀ c ∈ φ,
        (c.filter (fun l => xor l.2 (flip l.1) && decide (l.1 ∉ xs))).length ≤ 1} ∈ P ∧
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ xs : List ℕ, xs.length ≤ k ∧ ∃ flip : Assignment, ∀ c ∈ φ,
        (c.filter (fun l => xor l.2 (flip l.1) && decide (l.1 ∉ xs))).length ≤ 1) ∧
      Satisfiable φ} ∈ P := by
  let H : CNF → Prop := fun φ => ∃ flip : Assignment, ∀ c ∈ φ,
    ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1
  let G : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ H φ}
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ H φ ∧ Satisfiable φ}
  have hg (φ : CNF) : encodeCNF φ ∈ G ↔ H φ := by
    constructor
    · rintro ⟨f,he,h⟩
      exact encodeCNF_injective he ▸ h
    · exact fun h => ⟨φ,rfl,h⟩
  have hsub (φ ψ : CNF) (h : ψ.Sublist φ) (he : encodeCNF φ ∈ G) : encodeCNF ψ ∈ G := by
    obtain ⟨flip,hflip⟩ := (hg φ).mp he
    exact (hg ψ).mpr ⟨flip,fun c hc => hflip c (h.subset hc)⟩
  have hd (φ : CNF) (h : encodeCNF φ ∈ G) : encodeCNF φ ∈ D ↔ Satisfiable φ := by
    constructor
    · rintro ⟨f,he,_,hs⟩
      exact encodeCNF_injective he ▸ hs
    · exact fun hs => ⟨φ,rfl,(hg φ).mp h,hs⟩
  have hf (xs : List ℕ) (φ : CNF) :
      encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G ↔
      ∃ flip : Assignment, ∀ c ∈ φ,
        (c.filter (fun l => xor l.2 (flip l.1) && decide (l.1 ∉ xs))).length ≤ 1 := by
    rw [hg]
    constructor
    · rintro ⟨flip,h⟩
      refine ⟨flip,fun c hc => ?_⟩
      have h' := h _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
      simpa only [List.filter_map,List.length_map,Function.comp_apply,List.filter_filter,Bool.and_comm] using h'
    · rintro ⟨flip,h⟩
      refine ⟨flip,fun c hc => ?_⟩
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      simpa only [List.filter_map,List.length_map,Function.comp_apply,List.filter_filter,Bool.and_comm] using h d hd
  simpa only [hf] using ExactVariableDeletionSAT G D ExactRenamableHornGuard ExactRenamableHornSAT hsub hd k

end PEqualNP.Outside
