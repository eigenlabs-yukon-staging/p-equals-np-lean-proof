import PEqualNP.Outside.MeasuredEliminationWalk
import PEqualNP.Outside.MeasuredBoundedClauseUniverse
import PEqualNP.Outside.EliminationStageWidth
import PEqualNP.Outside.FullEliminationSAT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

/-- For fixed width, evaluate a supplied elimination order using an
automatically generated universe. Empty output certifies a width violation. -/
theorem MeasuredWidthElimination (k : ℕ) :
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ∃ run : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) run ∧
      ∀ (φ : CNF) (order : List ℕ),
        let bounded := ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl eliminate (clauses φ), Finset.card c ≤ k
        let result := run (encodeClause (order.map (fun x => (x,true))),encodeCNF φ)
        (result ≠ [] ↔ bounded) ∧
        (bounded → (∀ c ∈ clauses φ, ∀ l ∈ c, l.1 ∈ order) →
          (result = [true] ↔ PEqualNP.ProofComplexity.Satisfiable (clauses φ))) := by
  dsimp only
  obtain ⟨walk,hw,hws⟩ := MeasuredEliminationWalk
  obtain ⟨gen,hgen,hgs⟩ := MeasuredBoundedClauseUniverse k
  let raw := fun s : Raw => walk (pairB (unpairB s).1 (pairB (unpairB s).2 (gen (unpairB s).2)))
  have hraw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) raw :=
    cpt_comp (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_comp cpt_unpairB2 hgen))) hw
  let run := fun p : Raw × Raw => walk (pairB p.1 (pairB p.2 (gen p.2)))
  have hr : ComputableInPolyTime encodePair (fun x : Raw => x) run := by
    simpa only [raw,run,unpairB_pairB] using cpt_comp (g := raw) cpt_pairB hraw
  refine ⟨run,hr,fun φ order => ?_⟩
  obtain ⟨U,hU,hmem⟩ := hgs φ
  have hmain := hws φ U order
  let x := encodeClause (order.map (fun x => (x,true)))
  let result := walk (pairB x (pairB (encodeCNF φ) (encodeCNF U)))
  let stageAt := fun j : ℕ => (order.take j).foldl (fun G x => eliminateVariable x G) (clauseSet φ)
  have hwidth : (∀ j ≤ order.length, ∀ c ∈ stageAt j, Finset.card c ≤ k) ↔
      ∀ j ≤ order.length, stageAt j ⊆ clauseSet U := by
    have hmem' (c : Clause) : c ∈ U ↔ c.length ≤ k ∧ c ⊆ φ.flatten := by simpa using hmem c
    exact ⟨fun h j hj => (EliminationStageWidth k φ U (order.take j) hmem').mp (h j hj),
      fun h j hj => (EliminationStageWidth k φ U (order.take j) hmem').mpr (h j hj)⟩
  change (run (x,encodeCNF φ) ≠ [] ↔ ∀ j ≤ order.length, ∀ c ∈ stageAt j, Finset.card c ≤ k) ∧ _
  have heq : run (x,encodeCNF φ) = result := by simp [run,result,hU]
  rw [heq]
  have hw' : result ≠ [] ↔ ∀ j ≤ order.length, stageAt j ⊆ clauseSet U := hmain.1
  refine ⟨hw'.trans hwidth.symm,fun hb hc => ?_⟩
  obtain ⟨ψ,hψ,hset⟩ := hmain.2 (hw'.mpr (hwidth.mp hb))
  let final := order.foldl (fun G x => eliminateVariable x G) (clauseSet φ)
  have hs : PEqualNP.ProofComplexity.Satisfiable (clauseSet φ) ↔ final = ∅ :=
    FullEliminationSAT (clauseSet φ) order hc
  change clauseSet ψ = final at hset
  change result = true :: encodeCNF ψ at hψ
  change result = [true] ↔ PEqualNP.ProofComplexity.Satisfiable (clauseSet φ)
  refine Iff.trans ?_ hs.symm
  change result = [true] ↔ final = ∅
  rw [← hset,hψ,clauseSet_eq_empty_iff]
  constructor
  · intro h
    have hnil := (List.cons.inj h).2
    exact encodeCNF_injective (hnil.trans (show [] = encodeCNF [] by rfl))
  · rintro rfl
    rfl

end PEqualNP.Outside
