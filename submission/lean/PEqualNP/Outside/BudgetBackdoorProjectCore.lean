import PEqualNP.Outside.FixedBackdoorProjectCore
import PEqualNP.Library.L055

namespace PEqualNP.Outside.BudgetBackdoorProjectCore

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word pack formula code finish finish_cpt cut cut_cpt measure)
open PEqualNP.Outside.FixedBackdoorProjectCore (suffix probe formula_step step_growth)
open PEqualNP.Outside.AllFormulaNames (collect_cpt)
open PEqualNP.Outside.WidthDigitClock (skip_cpt lgU_cpt)
open PEqualNP.Outside.NameDigitClock (clock_cpt)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

theorem suffix_cpt : CPT suffix := by
  have hp : CPT probe := by
    unfold probe
    exact cpt_comp cpt_unpairB1 collect_cpt
  have h := cpt_comp hp clock_cpt
  have hb : CPT code := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  exact skip_cpt h hb

def step (z : Word) : Word := sel (suffix z) z (FixedBackdoorProjectCore.step z)

theorem step_cpt : CPT step := by
  exact cpt_sel suffix_cpt cpt_id FixedBackdoorProjectCore.step_cpt

theorem step_formula (z : Word) : formula (step z) = formula z := by
  unfold step sel
  split
  · rfl
  · exact formula_step z

theorem advance_length (z : Word) : (step z).length ≤ z.length + measure z := by
  unfold step sel
  split
  · omega
  · exact step_growth z

def unaryBudget (p : Polynomial ℕ) (x : Word) : Word := un (p.eval x.length)

theorem unaryBudget_cpt (p : Polynomial ℕ) : CPT (unaryBudget p) := L055 p

def cap (p : Polynomial ℕ) (x : Word) : Word := (lgU (unaryBudget p x)).tail

theorem cap_cpt (p : Polynomial ℕ) : CPT (cap p) := by
  have h := cpt_tail1 (cpt_comp (unaryBudget_cpt p) lgU_cpt)
  exact h

theorem cap_length (p : Polynomial ℕ) (x : Word) : (cap p x).length = (p.eval x.length).size - 1 := by
  simp [cap, unaryBudget, lgU_un, List.length_tail, un_length]

def endState (p : Polynomial ℕ) (q : Word × Word) : Word :=
  step^[q.2.length] (pack q.1 [] [] (cut (cap p q.1) q.2))

theorem endState_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun x : Word => x) (endState p) := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime_measure step m BackdoorPathCore.measure 4
    (fun z => by simp [BackdoorPathCore.measure, step_formula]) advance_length
    (fun z => by have h := unpairB_length z; simp only [BackdoorPathCore.measure, formula]; omega)
  have hcut := cut_cpt (cpt_comp cpt_unpairB1 (cap_cpt p)) cpt_unpairB2
  have seed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) hcut)))
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 [] [] (cut (cap p q.1) q.2)) :=
    cptl seed (fun q => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_pairG hs cpt_snd) loop
  exact h

def query (p : Polynomial ℕ) (q : Word × Word) : Word := finish (endState p q)

theorem query_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun x : Word => x) (query p) := by
  have h := cpt_comp (endState_cpt p) finish_cpt
  exact h

end PEqualNP.Outside.BudgetBackdoorProjectCore
