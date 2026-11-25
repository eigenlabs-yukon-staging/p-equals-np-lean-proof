import PEqualNP.Outside.MeasuredEliminationWitness
import PEqualNP.Outside.MeasuredBoundedClauseUniverse
import PEqualNP.Outside.EliminationStageWidth

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search

private abbrev Raw := List Bool

/-- Recover a checked sparse satisfying assignment using a fixed-width
elimination order, without requiring a candidate universe in the input. -/
theorem MeasuredWidthEliminationWitness (k : ℕ) :
    let varCode := fun i : ℕ => (i.bits.flatMap fun b => [true,b]) ++ [false,true]
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ∃ search : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) search ∧
      ∀ (φ : CNF) (order : List ℕ),
        (∀ c ∈ clauses φ, ∀ l ∈ c, l.1 ∈ order) →
        (∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl eliminate (clauses φ), Finset.card c ≤ k) →
        let result := search (encodeClause (order.map (fun x => (x,true))),encodeCNF φ)
        (result = [] ↔ ¬ Satisfiable φ) ∧
        (Satisfiable φ → ∃ vs : List ℕ, result = true :: vs.flatMap varCode ∧
          CNF.eval (fun x => decide (x ∈ vs)) φ = true) := by
  dsimp only
  obtain ⟨search,hs,hss⟩ := MeasuredEliminationWitness
  obtain ⟨gen,hg,hgs⟩ := MeasuredBoundedClauseUniverse k
  let raw := fun s : Raw => search (pairB (unpairB s).1 (pairB (unpairB s).2 (gen (unpairB s).2)))
  have hraw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) raw :=
    cpt_comp (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_comp cpt_unpairB2 hg))) hs
  let run := fun p : Raw × Raw => search (pairB p.1 (pairB p.2 (gen p.2)))
  have hr : ComputableInPolyTime encodePair (fun x : Raw => x) run := by
    simpa only [raw,run,unpairB_pairB] using cpt_comp (g := raw) cpt_pairB hraw
  refine ⟨run,hr,fun φ order hord hwidth => ?_⟩
  obtain ⟨U,hU,hrep⟩ := hgs φ
  have hsupp (c : Clause) : c ∈ U ↔ c.length ≤ k ∧ c ⊆ φ.flatten := by simpa using hrep c
  have hCovers (j : ℕ) (hj : j ≤ order.length) :
      (order.take j).foldl (fun G x => eliminateVariable x G) (clauseSet φ) ⊆ clauseSet U :=
    (EliminationStageWidth k φ U (order.take j) hsupp).mp (hwidth j hj)
  let o := encodeClause (order.map (fun x => (x,true)))
  let spec := fun r : Raw => (r = [] ↔ ¬ Satisfiable φ) ∧
    (Satisfiable φ → ∃ vs : List ℕ, r = true :: vs.flatMap
      (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
      CNF.eval (fun x => decide (x ∈ vs)) φ = true)
  change spec (run (o,encodeCNF φ))
  have heq : run (o,encodeCNF φ) = search (pairB o (pairB (encodeCNF φ) (encodeCNF U))) := by
    simp only [run,hU]
  rw [heq]
  exact hss φ U order hord hCovers

end PEqualNP.Outside
