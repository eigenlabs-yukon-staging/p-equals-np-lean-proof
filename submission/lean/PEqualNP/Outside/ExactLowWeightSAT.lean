import PEqualNP.Outside.MeasuredDistinctClauseVariables
import PEqualNP.Outside.MeasuredLowWeightSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search

/-- The exact language of satisfiable canonical low-weight CNFs without a repeated
variable in any clause belongs to the reference class P. -/
theorem ExactLowWeightSAT :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.map Prod.fst).Nodup) ∧
      (φ.map (fun c => (2 : ℚ)⁻¹ ^ c.length)).sum < 1 ∧ Satisfiable φ} ∈ P := by
  obtain ⟨distinct,hd,hds⟩ := MeasuredDistinctClauseVariables
  obtain ⟨light,hl,hls⟩ := MeasuredClauseWeight
  obtain ⟨search,_,hss⟩ := MeasuredLowWeightSearch
  let test := fun x => wfB x && distinct x && light x
  have htest := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_sel cpt_wfF (cpt_const [])
      (cpt_sel (cpt_bitFlag hd) (cpt_const []) (cpt_bitFlag hl))) bf_cpt_neL
  have he : (fun x => !(sel (bflag (wfB x)) [] (sel (if distinct x then [true] else [])
      [] (if light x then [true] else []))).isEmpty) = test := by
    funext x
    unfold test
    cases wfB x <;> cases distinct x <;> cases light x <;> rfl
  rw [he] at htest
  refine ⟨test,fun x => ?_,htest⟩
  change (∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.map Prod.fst).Nodup) ∧
      (φ.map (fun c => (2 : ℚ)⁻¹ ^ c.length)).sum < 1 ∧ Satisfiable φ) ↔ test x = true
  simp only [test,Bool.and_eq_true]
  constructor
  · rintro ⟨φ,rfl,hφ,hw,_⟩
    exact ⟨⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(hds φ).mpr hφ⟩,(hls φ).mpr hw⟩
  · rintro ⟨⟨hc,hdist⟩,hlight⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff _).mp hc
    have hp := (hds φ).mp hdist
    have hw := (hls φ).mp hlight
    obtain ⟨xs,_,_,hsol⟩ := hss φ hp hw
    exact ⟨φ,rfl,hp,hw,⟨fun x => decide (x ∈ xs),hsol⟩⟩

end PEqualNP.Outside
