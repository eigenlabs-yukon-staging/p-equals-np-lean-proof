import PEqualNP.Outside.MeasuredBoundedWidthRefutationSearch
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

/-- For a fixed width, the exact canonical language of CNFs admitting a
resolution refutation of that width belongs to the reference class P. -/
theorem ExactBoundedResolutionWidth (k : ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
        PEqualNP.ProofComplexity.IsRefutation
          {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
        ∀ d ∈ π, Finset.card d ≤ k} ∈ P := by
  obtain ⟨search,hs,hss⟩ := MeasuredBoundedWidthRefutationSearch k
  let test := fun x => wfB x && !(search x).isEmpty
  have ht := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_sel cpt_wfF (cpt_const []) hs) bf_cpt_neL
  have he : (fun x => !(sel (bflag (wfB x)) [] (search x)).isEmpty) = test := by
    funext x
    unfold test
    cases wfB x <;> rfl
  rw [he] at ht
  refine ⟨test,fun x => ?_,ht⟩
  change (∃ φ : CNF, encodeCNF φ = x ∧
    ∃ π : List FinClause, PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) π ∧
      ∀ d ∈ π, Finset.card d ≤ k) ↔ test x = true
  simp only [test,Bool.and_eq_true,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨φ,rfl,h⟩
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(hss φ).1.mpr h⟩
  · rintro ⟨hv,hn⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff _).mp hv
    exact ⟨φ,rfl,(hss φ).1.mp hn⟩

end PEqualNP.Outside
