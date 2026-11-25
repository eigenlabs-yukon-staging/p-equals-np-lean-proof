import PEqualNP.Outside.DavisPutnamElimination

namespace PEqualNP.Outside

open PEqualNP.ProofComplexity

theorem fold_elimination_satisfiable (F : Set NatClause) (order : List ℕ) :
    Satisfiable (order.foldl (fun G x => eliminateVariable x G) F) ↔ Satisfiable F := by
  induction order generalizing F with
  | nil => rfl
  | cons x xs ih =>
    exact (ih (eliminateVariable x F)).trans (DavisPutnamElimination x F)

private theorem final_empty_clauses (F : Set NatClause) (order : List ℕ)
    (h : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order) :
    ∀ d ∈ order.foldl (fun G x => eliminateVariable x G) F, d = ∅ := by
  induction order generalizing F with
  | nil =>
    intro d hd
    ext l
    have hn : l ∉ d := fun hl => by simpa using h d hd l hl
    simp [hn]
  | cons x xs ih =>
    apply ih
    intro d hd l hl
    obtain ⟨hne,c,hc,hl⟩ := eliminate_support hd l hl
    exact (List.mem_cons.mp (h c hc l hl)).resolve_left hne

/-- When the order covers the entire variable support, the formula is
satisfiable exactly when the final stage contains no clauses. -/
theorem FullEliminationSAT (F : Set (PEqualNP.ProofComplexity.Clause ℕ)) (order : List ℕ) :
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    (∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order) →
      (Satisfiable F ↔ order.foldl eliminate F = ∅) := by
  dsimp only
  intro h
  let final := order.foldl (fun G x => eliminateVariable x G) F
  change Satisfiable F ↔ final = ∅
  rw [← fold_elimination_satisfiable F order]
  change Satisfiable final ↔ final = ∅
  constructor
  · rintro ⟨a,ha⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨l,hl,_⟩ := ha d hd
    exact Finset.notMem_empty l (final_empty_clauses F order h d hd ▸ hl)
  · rintro hfinal
    refine ⟨fun _ => false,fun d hd => ?_⟩
    rw [hfinal] at hd
    exact hd.elim

end PEqualNP.Outside
