import PEqualNP.Outside.ExactProductBudgetSAT
import PEqualNP.Outside.SparseVariableSATSearch
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Library.Machines.ReduceNP

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Search

/-- A measured solver outputs a sparse satisfying assignment for a canonical SAT
instance whose wide-clause width product satisfies the polynomial budget. -/
theorem ProductBudgetSATSearch (q : Polynomial ℕ) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF,
        ((φ.filter (fun c => 2 < c.length)).map List.length).prod ≤ q.eval (encodeCNF φ).length →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    ((φ.filter (fun c => 2 < c.length)).map List.length).prod ≤ q.eval x.length ∧ Satisfiable φ}
  have hD : D ∈ P := ExactProductBudgetSAT q
  obtain ⟨f,hf,hs⟩ := SparseVariableSATSearch D hD
  refine ⟨f,hf,fun φ hbudget hsat => hs φ ?_ hsat⟩
  intro ls
  let extended := φ ++ ls.map (fun l : Literal => [l])
  change encodeCNF extended ∈ D ↔ Satisfiable extended
  have hw : (extended.filter (fun c => 2 < c.length)) = φ.filter (fun c => 2 < c.length) := by
    simp [extended, List.filter_append, List.filter_map, Function.comp_def]
  have hlen : (encodeCNF φ).length ≤ (encodeCNF extended).length := by
    simp [extended, encodeCNF, List.flatMap_append]
  have he : ((extended.filter (fun c => 2 < c.length)).map List.length).prod ≤
      q.eval (encodeCNF extended).length := by
    rw [hw]
    exact hbudget.trans (eval_mono q hlen)
  constructor
  · rintro ⟨F,henc,_,hF⟩
    exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective henc) ▸ hF
  · intro h
    exact ⟨extended,rfl,he,h⟩

end PEqualNP.Outside
