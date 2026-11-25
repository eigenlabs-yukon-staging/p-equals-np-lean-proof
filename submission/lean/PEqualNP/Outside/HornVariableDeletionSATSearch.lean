import PEqualNP.Outside.ExactHornVariableDeletionSAT
import PEqualNP.Outside.SparseVariableSATSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

private theorem deletion_append (k : ℕ) (φ : CNF) (ls : List Literal)
    (h : ∃ xs : List ℕ, xs.length ≤ k ∧ ∀ c ∈ φ,
      (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1) :
    ∃ xs : List ℕ, xs.length ≤ k ∧ ∀ c ∈ φ ++ ls.map (fun l => [l]),
      (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1 := by
  obtain ⟨xs,hxs,hc⟩ := h
  refine ⟨xs,hxs,fun c hm => ?_⟩
  rcases List.mem_append.mp hm with h | h
  · exact hc c h
  · obtain ⟨l,_,rfl⟩ := List.mem_map.mp h
    exact List.length_filter_le _ _

/-- Sparse satisfying assignments for formulas at fixed variable-deletion
distance from Horn. The deletion set need not be given as input. -/
theorem HornVariableDeletionSATSearch (k : ℕ) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∃ xs : List ℕ, xs.length ≤ k ∧ ∀ c ∈ φ,
        (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    (∃ xs : List ℕ, xs.length ≤ k ∧ ∀ c ∈ φ,
      (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1) ∧ Satisfiable φ}
  obtain ⟨search,hs,hc⟩ := SparseVariableSATSearch D (ExactHornVariableDeletionSAT k).2
  refine ⟨search,hs,fun φ h => hc φ (fun ls => ?_)⟩
  let ψ : CNF := φ ++ ls.map (fun l => [l])
  change encodeCNF ψ ∈ D ↔ Satisfiable ψ
  constructor
  · rintro ⟨f,he,_,hs⟩
    exact encodeCNF_injective he ▸ hs
  · intro hs
    exact ⟨ψ,rfl,deletion_append k φ ls h,hs⟩

end PEqualNP.Outside
