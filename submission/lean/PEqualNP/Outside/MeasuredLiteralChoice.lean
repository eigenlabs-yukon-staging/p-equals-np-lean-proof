import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def picked (r : List Bool) : List Bool :=
  if r.headD false then headI r ++ [false,false] else [false,false]

private theorem drop_nil (i : ℕ) : dropI^[i] ([] : List Bool) = [] := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, show dropI [] = [] by rfl, ih]

private theorem drop_literal (i : ℕ) (c : Clause) :
    dropI^[i] (encodeClause c) =
      if i ≤ c.length then encodeClause (c.drop i) else [] := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply]
      cases c with
      | nil => exact drop_nil i
      | cons a c =>
          have h : encodeClause (a :: c) = encodeLiteral a ++ encodeClause c := by simp [encodeClause]
          rw [h, dropI_lit, ih]
          simp

private theorem picked_exact (c : Clause) (i : ℕ) :
    picked (dropI^[i] (encodeClause c)) = encodeClause (c[i]?.toList) := by
  rw [drop_literal]
  by_cases hi : i < c.length
  · rw [ite_eq_left (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi, List.getElem?_eq_getElem hi]
    rw [show encodeClause (c[i] :: c.drop (i+1)) =
      encodeLiteral c[i] ++ encodeClause (c.drop (i+1)) by
        simp only [encodeClause, List.flatMap_cons, List.append_assoc]]
    have h : (encodeLiteral c[i] ++ encodeClause (c.drop (i+1))).headD false = true := rfl
    unfold picked
    rw [ite_eq_left h, headI_lit]
    simp [encodeClause]
  · have hget : c[i]? = none := List.getElem?_eq_none (Nat.le_of_not_gt hi)
    rw [hget]
    split
    · rename_i hle
      have hd : c.drop i = [] := List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hi)
      rw [hd]
      rfl
    · rfl

/-- Select the ith literal of a canonical clause as a unit clause. An out-of-range
index writes the empty clause, which no assignment can satisfy. -/
theorem MeasuredLiteralChoice :
    ∃ pick : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) pick ∧
      ∀ (c : Clause) (index : List Bool),
        pick (index, encodeClause c) = encodeClause (c[index.length]?.toList) := by
  let rest := fun s => dropI^[(unpairB s).1.length] (unpairB s).2
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) rest :=
    cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 cpt_unpairB2
  have hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => picked (rest s)) := by
    have hout := cpt_sel (cpt_hd1 hr) (cpt_const [false,false])
      (cpt_app2 (cpt_comp hr cpt_headI) (cpt_const [false,false]))
    refine cptE hout (fun s => ?_)
    cases rest s with
    | nil => rfl
    | cons b l => cases b <;> rfl
  refine ⟨fun z => picked (rest (pairB z.1 z.2)), cpt_comp (g := fun s => picked (rest s)) cpt_pairB hp, fun c i => ?_⟩
  simp only [rest, unpairB_pairB]
  exact picked_exact c i.length

end PEqualNP.Outside
