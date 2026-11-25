import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

/-- A unary clock and a uniform witness generator suffice to decide bounded existential search. -/
theorem IndexedWitnessProjection
    (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (clock : List Bool → List Bool)
    (hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) clock)
    (generate : List Bool × List Bool → List Bool)
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) generate) :
    {x : List Bool | ∃ i < (clock x).length, (x, generate (List.replicate i true, x)) ∈ R} ∈ P := by
  obtain ⟨f, hf, hcf⟩ := hR
  let check := fun s => f ((unpairB s).2, generate (unpairB s))
  have hcheck : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool check :=
    cpt_comp (cpt_pair cpt_unpairB2 (cpt_comp cpt_unpairB hg)) hcf
  let results := fun x => (List.range (clock x).length).flatMap
    (fun i => if check (pairB (un i) x) then [true] else [])
  have hresults : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) results :=
    cpt_flatMapRange (cpt_bitFlag hcheck) hc cpt_id
  refine ⟨fun x => !(results x).isEmpty, fun x => ?_, cpt_comp (f := results) (g := fun l : List Bool => !l.isEmpty) hresults bf_cpt_neL⟩
  have hflag (b : Bool) : (if b then [true] else []) = [] ↔ b = false := by
    cases b <;> simp
  simp [results, check, unpairB_pairB, List.flatMap_eq_nil_iff, hflag, un]
  exact exists_congr (fun i => and_congr_right (fun _ => hf _))

end PEqualNP.Outside
