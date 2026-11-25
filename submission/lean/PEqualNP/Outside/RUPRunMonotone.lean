import PEqualNP.Defs.SearchRUP

namespace PEqualNP.Outside

open PEqualNP.Search

private theorem force_mono {V : Type} {F G : Set (PEqualNP.ProofComplexity.Clause V)}
    {A : Set (PEqualNP.ProofComplexity.Literal V)} (h : F ⊆ G) {l : PEqualNP.ProofComplexity.Literal V}
    (hu : UPForces F A l) : UPForces G A l := by
  induction hu with
  | hyp hh => exact .hyp hh
  | unit hc hl _ ih => exact .unit (h hc) hl ih

private theorem rup_mono {V : Type} {F G : Set (PEqualNP.ProofComplexity.Clause V)}
    (h : F ⊆ G) {c : PEqualNP.ProofComplexity.Clause V} (hr : IsRUP F c) : IsRUP G c := by
  obtain ⟨d,hd,he⟩ := hr
  exact ⟨d,h hd,fun l hl => force_mono h (he l hl)⟩

/-- A canonical RUP learning run remains valid after adding arbitrary
axiom clauses to its original premise set. -/
theorem RUPRunMonotone {V : Type} {F G : Set (PEqualNP.ProofComplexity.Clause V)}
    (h : F ⊆ G) (ρ : List (PEqualNP.ProofComplexity.Clause V)) :
    IsRUPRun F ρ → IsRUPRun G ρ := by
  intro hr
  induction hr with
  | nil => exact .nil
  | learn hρ hstep ih =>
      apply IsRUPRun.learn ih
      exact rup_mono (Set.union_subset_union h subset_rfl) hstep

end PEqualNP.Outside
