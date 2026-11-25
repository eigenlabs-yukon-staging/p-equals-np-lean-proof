import PEqualNP.Outside.DavisPutnamElimination
import PEqualNP.Outside.UnitPropagationCorrect

namespace PEqualNP.Outside

open PEqualNP.Search

private theorem fold_support (F : Set NatClause) (order : List ℕ) :
    ∀ d ∈ order.foldl (fun G x => eliminateVariable x G) F, ∀ l ∈ d, ∃ c ∈ F, l ∈ c := by
  induction order generalizing F with
  | nil => exact fun d hd l hl => ⟨d,hd,hl⟩
  | cons x xs ih =>
    intro d hd l hl
    obtain ⟨c,hc,hl⟩ := ih (eliminateVariable x F) d hd l hl
    obtain ⟨_,e,he,hle⟩ := eliminate_support hc l hl
    exact ⟨e,he,hle⟩

/-- Every elimination stage of width at most k is represented by a
catalogue of all clauses of width at most k on the original signed support. -/
theorem EliminationStageWidth (k : ℕ) (φ U : CNF) (order : List ℕ) :
    let clauses := fun (formula : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ formula, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    (∀ c : Clause, c ∈ U ↔ c.length ≤ k ∧ c ⊆ φ.flatten) →
    ((∀ d ∈ order.foldl eliminate (clauses φ), Finset.card d ≤ k) ↔
    order.foldl eliminate (clauses φ) ⊆ clauses U) := by
  dsimp only
  intro hU
  change (∀ d ∈ order.foldl (fun G x => eliminateVariable x G) (clauseSet φ), d.card ≤ k) ↔
    order.foldl (fun G x => eliminateVariable x G) (clauseSet φ) ⊆ clauseSet U
  constructor
  · intro h d hd
    refine ⟨d.toList,(hU _).mpr ⟨by simpa using h d hd,?_⟩,Finset.toList_toFinset _⟩
    intro l hl
    obtain ⟨c,⟨p,hp,rfl⟩,hl⟩ := fold_support (clauseSet φ) order d hd l (Finset.mem_toList.mp hl)
    exact List.mem_flatten.mpr ⟨p,hp,List.mem_toFinset.mp hl⟩
  · intro h d hd
    obtain ⟨c,hc,rfl⟩ := h hd
    exact (List.toFinset_card_le c).trans ((hU c).mp hc).1

end PEqualNP.Outside
