import PEqualNP.Outside.MeasuredOccurrenceElimination
import PEqualNP.Outside.FirstOccurrenceEliminationWidth
import PEqualNP.Outside.MeasuredWidthEliminationWitness

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

/-- From the formula alone, recover a sparse model whenever each original
clause has bounded diameter in the formula's first-occurrence ranks. -/
theorem FirstOccurrenceLocalityWitness (k : ℕ) :
    let varCode := fun i : ℕ => (i.bits.flatMap fun b => [true,b]) ++ [false,true]
    ∃ run : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) run ∧
      ∀ φ : CNF,
        let order := φ.flatten.map Prod.fst
        (∀ c ∈ φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k) →
        let result := run (encodeCNF φ)
        (result = [] ↔ ¬ Satisfiable φ) ∧
        (Satisfiable φ → ∃ vs : List ℕ, result = true :: vs.flatMap varCode ∧
          CNF.eval (fun x => decide (x ∈ vs)) φ = true) := by
  dsimp only
  obtain ⟨run,hr,hrs⟩ := MeasuredWidthEliminationWitness (2*(k+1))
  obtain ⟨normalize,hn,hns⟩ := MeasuredVariableOrderCode
  refine ⟨fun s => run (normalize s,s),cpt_comp (cpt_pair hn cpt_id) hr,fun φ hLoc => ?_⟩
  let order := φ.flatten.map Prod.fst
  have heq : normalize (encodeCNF φ) = encodeClause (order.map (fun x => (x,true))) := by
    rw [hns]
    simp only [order,List.map_map,Function.comp_def]
  have hFin : ∀ c ∈ clauseSet φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k := by
    rintro c ⟨d,hd,rfl⟩ l hl m hm
    exact hLoc d hd l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm)
  have hWidth := FirstOccurrenceEliminationWidth k (clauseSet φ) order hFin (occurrence_order_covers φ)
  let spec := fun r : List Bool => (r = [] ↔ ¬ Satisfiable φ) ∧
    (Satisfiable φ → ∃ vs : List ℕ, r = true :: vs.flatMap
      (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
      CNF.eval (fun x => decide (x ∈ vs)) φ = true)
  change spec (run (normalize (encodeCNF φ),encodeCNF φ))
  rw [heq]
  exact hrs φ order (occurrence_order_covers φ) hWidth

end PEqualNP.Outside
