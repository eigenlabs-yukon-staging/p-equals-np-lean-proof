import PEqualNP.Outside.PositiveClauseCollector
import PEqualNP.Outside.BackdoorPathCore

namespace PEqualNP.Outside.HornPropagationCore

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.BackdoorPathCore (Word pack finish finish_cpt cut cut_eq cut_cpt)
open PEqualNP.Outside.PositiveClauseCollector (gather gather_cpt)
open PEqualNP.Outside.SatCodePrimitives (cptl)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def residual (z : Word) : Word :=
  let x := (unpairB z).1
  let names := (unpairB z).2
  finish (pack x names names [])

theorem residual_cpt : CPT residual := by
  have hs := cpt_pairB2 cpt_unpairB1
    (cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have h := cpt_comp hs finish_cpt
  exact h

def unitName (z : Word) : Word := cut (unpairB z).1 (gather true (residual z))

theorem unitName_cpt : CPT unitName := cut_cpt cpt_unpairB1 (cpt_comp residual_cpt (gather_cpt true))

def step (z : Word) : Word :=
  let x := (unpairB z).1
  let names := (unpairB z).2
  let u := unitName z
  sel u z (pairB x (names ++ u))

theorem step_cpt : CPT step := by
  have hnew := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 unitName_cpt)
  exact cptl (cpt_sel unitName_cpt cpt_id hnew) (fun _ => rfl)

def measure (z : Word) : ℕ := (unpairB z).1.length + 1

theorem measure_step (z : Word) : measure (step z) ≤ measure z := by
  unfold measure step sel
  dsimp only
  split
  · rfl
  · simp [unpairB_pairB]

theorem step_length (z : Word) : (step z).length ≤ z.length + measure z := by
  have hp := unpairB_length z
  have hname : (unitName z).length ≤ (unpairB z).1.length := by
    simp [unitName, cut_eq, List.length_take]
  unfold step sel
  dsimp only
  split
  · omega
  · simp only [pairB_length, List.length_append, measure]
    omega

def endState (x : Word) : Word := step^[x.length] (pairB x [])

theorem endState_cpt : CPT endState := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime_measure step m measure 1 measure_step step_length
    (fun z => by have hp := unpairB_length z; unfold measure; omega)
  have hs := cpt_pairB2 cpt_id (cpt_const [])
  have h := cpt_comp (cpt_pair hs cpt_id) loop
  exact h

def obstruction (x : Word) : Word := gather false (residual (endState x))

theorem obstruction_cpt : CPT obstruction := by
  have h := cpt_comp (cpt_comp endState_cpt residual_cpt) (gather_cpt false)
  exact h

end PEqualNP.Outside.HornPropagationCore
