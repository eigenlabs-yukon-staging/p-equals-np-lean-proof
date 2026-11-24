import PEqualNP.Outside.WidthDigitClock
import PEqualNP.Outside.BinaryNameChoice
import PEqualNP.Outside.WeakWideMachine

namespace PEqualNP.Outside.WidthPathCore

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore
open PEqualNP.Outside.WidthDigitClock (digitClock digitClock_cpt skip skip_eq skip_cpt)
open PEqualNP.Outside.BinaryNameChoice (choose choose_cpt)
open PEqualNP.Outside.WeakWideMachine (probe)
open PEqualNP.Outside.FirstWideCollector (gather_cpt)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def indices (z : Word) : Word :=
  cut (digitClock (formula z)) (BackdoorPathCore.code z)

def suffix (z : Word) : Word :=
  skip (digitClock (formula z)) (BackdoorPathCore.code z)

def chooser (z : Word) : Word := choose (probe z, indices z)

def step (z : Word) : Word :=
  let x := formula z
  let s := selected z
  let t := setTrue z
  let b := suffix z
  let v := cut x (chooser z)
  let add := sel (bflag (b.headD false)) [] v
  sel (probe z) z (pack x (s ++ v) (t ++ add) b.tail)

theorem step_cpt : CPT step := by
  have hx : CPT formula := cpt_unpairB1
  have hs : CPT selected := cpt_unpairB1_1 cpt_unpairB2
  have q₃ := cpt_unpairB2_1 cpt_unpairB2
  have ht : CPT setTrue := cpt_unpairB1_1 q₃
  have hb : CPT BackdoorPathCore.code := cpt_unpairB2_1 q₃
  have hclock := cpt_comp hx digitClock_cpt
  have hindices : CPT indices := cut_cpt hclock hb
  have hSuffix : CPT suffix := skip_cpt hclock hb
  have hsco := cpt_comp finish_cpt gather_cpt
  have hchoose : CPT chooser := by
    have h := cpt_comp (cpt_pair hsco hindices) choose_cpt
    exact h
  have hv := cut_cpt hx hchoose
  have htrue := cpt_sel (cpt_comp hSuffix cpt_firstF) (cpt_const []) hv
  have hnew := cpt_pairB2 hx (cpt_pairB2 (cpt_app2 hs hv)
    (cpt_pairB2 (cpt_app2 ht htrue) (cpt_tail1 hSuffix)))
  exact cptl (cpt_sel hsco cpt_id hnew) (fun _ => rfl)

theorem formula_step (z : Word) : formula (step z) = formula z := by
  simp only [step, sel]
  split
  · rfl
  · simp [formula, pack, unpairB_pairB]

theorem step_growth (z : Word) : (step z).length ≤ z.length + BackdoorPathCore.measure z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  let v := cut (formula z) (chooser z)
  have hv : v.length ≤ (formula z).length := by simp [v, cut_eq, List.length_take]
  have htrue : (sel (bflag ((suffix z).headD false)) [] v).length ≤ v.length := by
    unfold sel
    split <;> simp
  have hcode : (suffix z).length ≤ (BackdoorPathCore.code z).length := by
    simp [suffix, skip_eq]
  change (sel (probe z) z (pack (formula z) (selected z ++ v)
      (setTrue z ++ sel (bflag ((suffix z).headD false)) [] v) (suffix z).tail)).length ≤ _
  unfold sel at htrue ⊢
  split
  · omega
  · simp only [pack, pairB_length, List.length_append, List.length_tail,
      BackdoorPathCore.measure, formula, selected, setTrue, BackdoorPathCore.code] at hv htrue hcode ⊢
    omega

def endState (q : Word × Word) : Word := step^[q.2.length] (pack q.1 [] [] q.2)

theorem endState_cpt : ComputableInPolyTime encodePair (fun x : Word => x) endState := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime_measure step m BackdoorPathCore.measure 4
    (fun z => by simp [BackdoorPathCore.measure, formula_step]) step_growth
    (fun z => by have h := unpairB_length z; simp only [BackdoorPathCore.measure, formula]; omega)
  have seed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) cpt_unpairB2)))
  have hseed : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 [] [] q.2) :=
    cptl seed (fun q => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_pairG hseed cpt_snd) loop
  exact h

def query (q : Word × Word) : Word := finish (endState q)

theorem query_cpt : ComputableInPolyTime encodePair (fun x : Word => x) query :=
  by unfold query; exact cpt_comp WidthPathCore.endState_cpt finish_cpt

end PEqualNP.Outside.WidthPathCore
