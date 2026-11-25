import PEqualNP.Outside.ExactRenamableHornSAT
import PEqualNP.Outside.SparseVariableSATSearch
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Search

private def renamable (φ : CNF) : Prop :=
  ∃ flip : Assignment, ∀ c ∈ φ,
    ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1

private theorem renamable_units (φ : CNF) (ls : List Literal) (h : renamable φ) :
    renamable (φ ++ ls.map (fun l => [l])) := by
  obtain ⟨flip,hf⟩ := h
  refine ⟨flip,fun c hc => ?_⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact hf c hc
  · obtain ⟨l,_,rfl⟩ := List.mem_map.mp hc
    exact (List.length_filter_le _ _).trans (by simp)

/-- A measured sparse witness producer for satisfiable renamable Horn instances. -/
theorem RenamableHornSATSearch :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF,
        (∃ flip : Assignment, ∀ c ∈ φ,
          ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ renamable φ ∧ Satisfiable φ}
  have hD : D ∈ P := ExactRenamableHornSAT
  obtain ⟨f,hf,hsearch⟩ := SparseVariableSATSearch D hD
  refine ⟨f,hf,fun φ hRen hSat => hsearch φ ?_ hSat⟩
  intro ls
  constructor
  · rintro ⟨F,henc,_,hs⟩
    exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective henc) ▸ hs
  · intro hs
    exact ⟨φ ++ ls.map (fun l => [l]),rfl,renamable_units φ ls hRen,hs⟩

end PEqualNP.Outside
