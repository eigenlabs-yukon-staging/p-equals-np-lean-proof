import PEqualNP.Outside.MeasuredVariableDeletionSAT
import PEqualNP.Library.L046
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search

private theorem exact_from_measured (Y : CNF → Prop) (test : List Bool → Bool)
    (ht : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test)
    (hp : ∀ φ : CNF, test (encodeCNF φ) = true ↔ Y φ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Y φ} ∈ P := by
  let E : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  let D : Language Bool := {x | test x = true}
  have hw := cpt_comp (g := fun w : List Bool => !w.isEmpty) cpt_wfF bf_cpt_neL
  have hcanon : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
    funext s
    cases wfB s <;> rfl
  rw [hcanon] at hw
  have hE : E ∈ P := ⟨wfB,fun s => (wfB_iff s).symm,hw⟩
  have hD : D ∈ P := ⟨test,fun _ => Iff.rfl,ht⟩
  have he : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Y φ} = E ⊓ D := by
    ext x
    change (∃ φ, encodeCNF φ = x ∧ Y φ) ↔ (∃ φ, encodeCNF φ = x) ∧ test x = true
    constructor
    · rintro ⟨φ,rfl,h⟩
      exact ⟨⟨φ,rfl⟩,(hp φ).mpr h⟩
    · rintro ⟨⟨φ,rfl⟩,h⟩
      exact ⟨φ,rfl,(hp φ).mp h⟩
  rw [he]
  exact L046 E D hE hD

/-- Fixed-size occurrence deletion lifts both a measured structural guard and
its measured SAT decider to exact languages of canonical formula encodings. -/
theorem ExactVariableDeletionSAT (G D : Language Bool) (hG : G ∈ P) (hD : D ∈ P)
    (hsub : ∀ φ ψ : CNF, ψ.Sublist φ → encodeCNF φ ∈ G → encodeCNF ψ ∈ G)
    (hDspec : ∀ φ : CNF, encodeCNF φ ∈ G → (encodeCNF φ ∈ D ↔ Satisfiable φ)) (k : ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ xs : List ℕ, xs.length ≤ k ∧ encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G} ∈ P ∧
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ xs : List ℕ, xs.length ≤ k ∧ encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G) ∧
      Satisfiable φ} ∈ P := by
  obtain ⟨test,ht,hs⟩ := MeasuredVariableDeletionSAT G D hG hD hsub hDspec k
  constructor
  · refine exact_from_measured _ (fun x => test (x,[])) (cpt_comp (cpt_pair cpt_id (cpt_const [])) ht) (fun φ => ?_)
    have h := hs φ [] (List.nil_sublist _)
    have hSat : Satisfiable [] := ⟨fun _ => false,rfl⟩
    simpa only [hSat,and_true,show encodeCNF [] = [] by rfl] using h
  · exact exact_from_measured _ (fun x => test (x,x)) (cpt_comp (cpt_pair cpt_id cpt_id) ht)
      (fun φ => hs φ φ (List.Sublist.refl _))

end PEqualNP.Outside
