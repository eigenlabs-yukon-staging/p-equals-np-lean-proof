import PEqualNP.Outside.MeasuredWidthElimination
import PEqualNP.Outside.MeasuredVariableOrderCode
import PEqualNP.Outside.EliminationAssignmentLift

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private abbrev Raw := List Bool

theorem occurrence_order_covers (φ : CNF) :
    ∀ c ∈ clauseSet φ, ∀ l ∈ c, l.1 ∈ φ.flatten.map Prod.fst := by
  rintro c ⟨d,hd,rfl⟩ l hl
  exact List.mem_map.mpr ⟨l,List.mem_flatten.mpr ⟨d,hd,List.mem_toFinset.mp hl⟩,rfl⟩

/-- Obtain the variable order from the input's literal sequence and check
its fixed intermediate width, deciding satisfiability when it is bounded. -/
theorem MeasuredOccurrenceElimination (k : ℕ) :
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ∃ run : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) run ∧
      ∀ φ : CNF,
        let order := φ.flatten.map Prod.fst
        let result := run (encodeCNF φ)
        let width := ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl eliminate (clauses φ), Finset.card c ≤ k
        (result ≠ [] ↔ width) ∧ (result = [true] ↔ width ∧ Satisfiable φ) := by
  dsimp only
  obtain ⟨run,hr,hrs⟩ := MeasuredWidthElimination k
  obtain ⟨orderWord,ho,hos⟩ := MeasuredVariableOrderCode
  let execute := fun s : Raw => run (orderWord s,s)
  refine ⟨execute,cpt_comp (cpt_pair ho cpt_id) hr,fun φ => ?_⟩
  let order := φ.flatten.map Prod.fst
  have heq : orderWord (encodeCNF φ) = encodeClause (order.map (fun x => (x,true))) := by
    rw [hos]
    simp only [order,List.map_map,Function.comp_def]
  let result := execute (encodeCNF φ)
  let width := ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl
    (fun G x => eliminateVariable x G) (clauseSet φ), Finset.card c ≤ k
  have hsat : PEqualNP.ProofComplexity.Satisfiable (clauseSet φ) ↔ Satisfiable φ :=
    ⟨fun ⟨a,h⟩ => ⟨a,(cnf_satisfies_iff a φ).mpr h⟩,fun ⟨a,h⟩ => ⟨a,(cnf_satisfies_iff a φ).mp h⟩⟩
  have hres : result = run (encodeClause (order.map (fun x => (x,true))),encodeCNF φ) := by
    simp only [result,execute,heq]
  have hh : (result ≠ [] ↔ width) ∧ (width → (result = [true] ↔ PEqualNP.ProofComplexity.Satisfiable (clauseSet φ))) := by
    rw [hres]
    exact ⟨(hrs φ order).1,fun hw => (hrs φ order).2 hw (occurrence_order_covers φ)⟩
  change (result ≠ [] ↔ width) ∧ (result = [true] ↔ width ∧ Satisfiable φ)
  refine ⟨hh.1,⟨?_,?_⟩⟩
  · intro h
    have hn : result ≠ [] := by rw [h]; decide
    exact ⟨hh.1.mp hn,hsat.mp ((hh.2 (hh.1.mp hn)).mp h)⟩
  · rintro ⟨hw,hs⟩
    exact (hh.2 hw).mpr (hsat.mpr hs)

end PEqualNP.Outside
