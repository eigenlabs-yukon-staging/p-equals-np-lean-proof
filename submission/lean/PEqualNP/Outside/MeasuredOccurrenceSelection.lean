import PEqualNP.Outside.MeasuredOccurrenceNumbering
import PEqualNP.Outside.RecordAttachQuery
import PEqualNP.Outside.RecordMapMachine
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF)
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.RecordAttachQuery (attach attach_cpt attach_enc)
open PEqualNP.Outside.RecordMapMachine (flatMapWord flatMapWord_cpt flatMapWord_enc)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def selectOne (s : Word) : Word :=
  let q := unpairB s
  let r := unpairB q.2
  sel (bflag (decide (q.1 = r.1))) [] (pairB r.2 [])

theorem selectOne_cpt : CPT selectOne := by
  have ha := cpt_unpairB1
  have hb := cpt_unpairB1_1 cpt_unpairB2
  have hc := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_sel (cpt_eqF ha hb) (cpt_const [])
    (cpt_pairB2 hc (cpt_const []))) (fun _ => rfl)

def selectLabels (q : Word × Word) : Word := flatMapWord selectOne (attach q)

theorem selectLabels_cpt : ComputableInPolyTime encodePair (fun w : Word => w) selectLabels := by
  unfold selectLabels
  exact cpt_comp attach_cpt (flatMapWord_cpt selectOne selectOne_cpt)

def selected (key : Word) (xs : List Word) : List Word :=
  (xs.filter fun r => (unpairB r).1 == key).map fun r => (unpairB r).2

theorem selectLabels_enc (key : Word) (xs : List Word) :
    selectLabels (key,wire xs) = wire (selected key xs) := by
  rw [selectLabels,attach_enc,flatMapWord_enc selectOne
    (fun s => if (unpairB s).1 = (unpairB (unpairB s).2).1 then [(unpairB (unpairB s).2).2] else [])
    (fun s => by
      by_cases h : (unpairB s).1 = (unpairB (unpairB s).2).1 <;>
        simp [selectOne,h,bflag,sel,wire])]
  apply congrArg wire
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,List.flatMap_cons,unpairB_pairB]
    rw [ih]
    by_cases h : key = (unpairB r).1
    · simp [h,selected]
    · simp [h,Ne.symm h,selected]

end PEqualNP.Outside.OccurrenceSplit
