import PEqualNP.Outside.MeasuredTwoSATBackdoor
import PEqualNP.Library.L046

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

private theorem exact_from_test (Y : CNF → Prop) (test : List Bool → Bool)
    (ht : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test)
    (hs : ∀ φ : CNF, test (encodeCNF φ) = true ↔ Y φ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Y φ} ∈ P := by
  let D : Language Bool := {x | test x = true}
  let E : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  have ht' := cpt_comp (g := fun w : List Bool => !w.isEmpty) cpt_wfF bf_cpt_neL
  have hcanon : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
    funext s
    cases wfB s <;> rfl
  rw [hcanon] at ht'
  have hE : E ∈ P := ⟨wfB,fun s => (wfB_iff s).symm,ht'⟩
  have hD : D ∈ P := ⟨test,fun _ => Iff.rfl,ht⟩
  have he : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Y φ} = E ⊓ D := by
    ext x
    change (∃ φ, encodeCNF φ = x ∧ Y φ) ↔ (∃ φ, encodeCNF φ = x) ∧ test x = true
    constructor
    · rintro ⟨φ,rfl,h⟩
      exact ⟨⟨φ,rfl⟩,(hs φ).mpr h⟩
    · rintro ⟨⟨φ,rfl⟩,h⟩
      exact ⟨φ,rfl,(hs φ).mp h⟩
  rw [he]
  exact L046 E D hE hD

/-- For a fixed deletion budget, both the exact canonical domain and its
satisfiable subset have measured deterministic polynomial-time deciders. -/
theorem ExactTwoSATBackdoor (k : ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))} ∈ P ∧
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧
      Satisfiable φ} ∈ P := by
  obtain ⟨test,ht,hs⟩ := MeasuredTwoSATBackdoor k
  constructor
  · refine exact_from_test _ (fun x => test (x,[]))
      (cpt_comp (cpt_pair cpt_id (cpt_const [])) ht) (fun φ => ?_)
    have h := hs φ [] (List.nil_sublist _)
    have hSat : Satisfiable [] := ⟨fun _ => false,rfl⟩
    simpa [hSat, show encodeCNF [] = [] by rfl] using h
  · exact exact_from_test _ (fun x => test (x,x)) (cpt_comp (cpt_pair cpt_id cpt_id) ht)
      (fun φ => hs φ φ (List.Sublist.refl _))

end PEqualNP.Outside
