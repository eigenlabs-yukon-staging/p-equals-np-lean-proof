import PEqualNP.Outside.BackdoorPathCore

namespace PEqualNP.Outside.BackdoorRecordCore

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def advanceRecord (probe choose : Word → Word) (z : Word) : Word :=
  let x := formula z
  let s := selected z
  let t := setTrue z
  let b := unpairB (BackdoorPathCore.code z)
  let v := cut x (choose z)
  let add := sel (bflag ((b.1).headD false)) [] v
  sel (probe z) z (pack x (s ++ v) (t ++ add) b.2)

theorem advanceRecord_cpt {probe choose : Word → Word}
    (hq : CPT probe) (hchoose : CPT choose) : CPT (advanceRecord probe choose) := by
  have hx : CPT formula := cpt_unpairB1
  have hs : CPT selected := cpt_unpairB1_1 cpt_unpairB2
  have q₃ := cpt_unpairB2_1 cpt_unpairB2
  have ht : CPT setTrue := cpt_unpairB1_1 q₃
  have hb : CPT BackdoorPathCore.code := cpt_unpairB2_1 q₃
  have hv := cut_cpt hx hchoose
  have htrue := cpt_sel (cpt_comp (cpt_unpairB1_1 hb) cpt_firstF) (cpt_const []) hv
  have hnew := cpt_pairB2 hx (cpt_pairB2 (cpt_app2 hs hv)
    (cpt_pairB2 (cpt_app2 ht htrue) (cpt_unpairB2_1 hb)))
  exact cptl (cpt_sel hq cpt_id hnew) (fun _ => rfl)

theorem formula_advance (probe choose : Word → Word) (z : Word) :
    formula (advanceRecord probe choose z) = formula z := by
  simp only [advanceRecord, sel]
  split
  · rfl
  · simp [formula, pack, unpairB_pairB]

theorem advance_growth (probe choose : Word → Word) (z : Word) :
    (advanceRecord probe choose z).length ≤ z.length + BackdoorPathCore.measure z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  have hb := unpairB_length (BackdoorPathCore.code z)
  simp only [BackdoorPathCore.code] at hb
  let v := cut (formula z) (choose z)
  have hv : v.length ≤ (formula z).length := by simp [v, cut_eq, List.length_take]
  have htrue : (sel (bflag (((unpairB (BackdoorPathCore.code z)).1).headD false)) [] v).length ≤ v.length := by
    unfold sel
    split <;> simp
  change (sel (probe z) z
      (pack (formula z) (selected z ++ v)
        (setTrue z ++ sel (bflag (((unpairB (BackdoorPathCore.code z)).1).headD false)) [] v)
        (unpairB (BackdoorPathCore.code z)).2)).length ≤ z.length + BackdoorPathCore.measure z
  unfold sel at htrue ⊢
  split
  · omega
  · simp only [pack, pairB_length, List.length_append, List.length_drop, BackdoorPathCore.measure,
      formula, selected, setTrue, BackdoorPathCore.code] at hv htrue ⊢
    omega

def endStateRecord (probe choose : Word → Word) (q : Word × Word) : Word :=
  (advanceRecord probe choose)^[q.2.length] (pack q.1 [] [] q.2)

theorem endStateRecord_cpt {probe choose : Word → Word} (hp : CPT probe) (hc : CPT choose) :
    ComputableInPolyTime encodePair (fun x : Word => x) (endStateRecord probe choose) := by
  obtain ⟨m⟩ := advanceRecord_cpt hp hc
  have loop := Iter.iter_polyTime_measure (advanceRecord probe choose) m BackdoorPathCore.measure 4
    (fun z => by simp [BackdoorPathCore.measure, BackdoorRecordCore.formula_advance])
    (BackdoorRecordCore.advance_growth probe choose)
    (fun z => by have h := unpairB_length z; simp only [BackdoorPathCore.measure, formula]; omega)
  have seed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) cpt_unpairB2)))
  have hseed : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 [] [] q.2) :=
    cptl seed (fun q => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_pairG hseed cpt_snd) loop
  exact h

end PEqualNP.Outside.BackdoorRecordCore
