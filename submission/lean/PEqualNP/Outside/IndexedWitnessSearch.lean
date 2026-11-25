import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

private theorem flatMap_nil_of_reject (test : ℕ → Bool) (word : ℕ → List Bool)
    (indices : List ℕ) (h : ∀ i ∈ indices, test i = false) :
    indices.flatMap (fun i => if test i then pairB (word i) [] else []) = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro i hi
  simp [h i hi]

private theorem flatMap_first_record (test : ℕ → Bool) (word : ℕ → List Bool)
    (n i : ℕ) (hi : i < n) (ht : test i = true)
    (hfirst : ∀ j < i, test j = false) :
    ∃ tail : List Bool,
      (List.range n).flatMap (fun j => if test j then pairB (word j) [] else []) =
        pairB (word i) tail := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      by_cases hin : i < n
      · obtain ⟨tail, htail⟩ := ih hin
        rw [htail]
        exact ⟨tail ++ (if test n then pairB (word n) [] else []), by simp [pairB, List.append_assoc]⟩
      · have he : i = n := by omega
        subst i
        have hbefore := flatMap_nil_of_reject test word (List.range n)
          (fun j hj => hfirst j (List.mem_range.mp hj))
        rw [hbefore]
        exact ⟨[], by simp [ht]⟩

/-- A measured search returns the witness at the first accepting unary index.
The tag distinguishes an accepting empty witness from an exhausted search. -/
theorem IndexedWitnessSearch
    (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (clock : List Bool → List Bool)
    (hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) clock)
    (generate : List Bool × List Bool → List Bool)
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) generate) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      (∀ x : List Bool,
        (∀ i < (clock x).length, (x, generate (List.replicate i true, x)) ∉ R) →
        search x = []) ∧
      ∀ (x : List Bool) (i : ℕ), i < (clock x).length →
        (x, generate (List.replicate i true, x)) ∈ R →
        (∀ j < i, (x, generate (List.replicate j true, x)) ∉ R) →
        search x = true :: generate (List.replicate i true, x) := by
  obtain ⟨f, hf, hcf⟩ := hR
  let candidate := fun s => generate (unpairB s)
  let verdict := fun s => f ((unpairB s).2, candidate s)
  have hcand : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) candidate :=
    cpt_comp cpt_unpairB hg
  have htest : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool verdict :=
    cpt_comp (cpt_pair cpt_unpairB2 hcand) hcf
  let record := fun s => if verdict s then pairB (candidate s) [] else []
  have hrecord : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) record := by
    refine cptE (cpt_sel (cpt_bitFlag htest) (cpt_const [])
      (cpt_pairB2 hcand (cpt_const []))) (fun s => ?_)
    cases h : verdict s <;> simp [sel, record, h]
  let collect := fun x => (List.range (clock x).length).flatMap (fun i => record (pairB (un i) x))
  have hcollect : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) collect :=
    cpt_flatMapRange hrecord hc cpt_id
  let finish := fun s => if s = [] then [] else true :: (unpairB s).1
  have hfinish : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) finish :=
    cpt_sel cpt_id (cpt_const []) (cpt_cons1 true cpt_unpairB1)
  have hsem (x : List Bool) :
      collect x = (List.range (clock x).length).flatMap
        (fun i => if f (x, generate (un i, x)) then pairB (generate (un i, x)) [] else []) := by
    simp only [collect, record, verdict, candidate, unpairB_pairB]
  refine ⟨fun x => finish (collect x), cpt_comp hcollect hfinish, ?_, ?_⟩
  · intro x hx
    change finish (collect x) = []
    rw [hsem, flatMap_nil_of_reject]
    · rfl
    · intro i hi
      have hn := hx i (List.mem_range.mp hi)
      exact Bool.eq_false_iff.mpr (fun h => hn ((hf _).mpr h))
  · intro x i hi hp hfirst
    have htestFirst : ∀ j < i, f (x, generate (un j, x)) = false := by
      intro j hj
      exact Bool.eq_false_iff.mpr (fun h => hfirst j hj ((hf _).mpr h))
    obtain ⟨tail, htail⟩ := flatMap_first_record
      (fun j => f (x, generate (un j, x))) (fun j => generate (un j, x))
      (clock x).length i hi ((hf _).mp hp) htestFirst
    change finish (collect x) = _
    rw [hsem, htail]
    have hne : pairB (generate (un i, x)) tail ≠ [] := by
      intro h
      have hl := pairB_length (generate (un i, x)) tail
      rw [h] at hl
      simp at hl
    unfold finish
    rw [if_neg hne, unpairB_pairB]
    rfl

end PEqualNP.Outside
