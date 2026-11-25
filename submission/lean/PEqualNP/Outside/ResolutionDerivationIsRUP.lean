import PEqualNP.Defs.SearchRUP

namespace PEqualNP.Outside

open PEqualNP.ProofComplexity PEqualNP.Search

private theorem resolvent_rup {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {C D R : Clause V} (hC : C ∈ F) (hD : D ∈ F) (hR : IsResolvent C D R) :
    IsRUP F R := by
  obtain ⟨v,hp,hn,rfl⟩ := hR
  let R := C.erase (v,true) ∪ D.erase (v,false)
  let A := negLit '' (↑R : Set (Literal V))
  have hP : UPForces F A (v,true) := by
    refine .unit (D := C) hC hp (fun l hl hne => .hyp ?_)
    exact ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne,hl⟩),rfl⟩
  refine ⟨D,hD,fun l hl => ?_⟩
  by_cases he : l = (v,false)
  · subst l
    exact hP
  · exact .hyp ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he,hl⟩),rfl⟩

/-- Every resolution derivation is a RUP learning run with the same clauses
in the same newest-first order. -/
theorem ResolutionDerivationIsRUP {V : Type} [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V))
    (ρ : List (PEqualNP.ProofComplexity.Clause V)) :
    PEqualNP.ProofComplexity.IsDerivation F ρ → IsRUPRun F ρ := by
  intro h
  induction h with
  | nil => exact .nil
  | @ax π C _ hC ih =>
      apply IsRUPRun.learn ih
      exact ⟨C,Or.inl hC,fun l hl => .hyp ⟨l,hl,rfl⟩⟩
  | @res π C D R _ hC hD hR ih =>
      exact .learn ih (resolvent_rup (Or.inr hC) (Or.inr hD) hR)

end PEqualNP.Outside
