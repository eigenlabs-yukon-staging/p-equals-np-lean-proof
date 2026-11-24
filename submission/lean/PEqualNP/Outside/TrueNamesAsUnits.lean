import PEqualNP.Outside.CnfRestrictionSemantics
import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.TrueNamesAsUnits

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionSemantics (names)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (z : Word) : Word :=
  let r := (unpairB z).1
  let a := (unpairB z).2
  sel r z (pairB (dropI r) (a ++ (true :: true :: headI r) ++ [false, false]))

theorem step_cpt : CPT step := by
  have hhead := cpt_cons1 true (cpt_cons1 true (cpt_comp cpt_unpairB1 cpt_headI))
  have ha := cpt_app2 (cpt_app2 cpt_unpairB2 hhead) (cpt_const [false, false])
  have hs := cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropI) ha
  exact cptl (cpt_sel cpt_unpairB1 cpt_id hs) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 5 := by
  have hw := unpairB_length z
  have h := congrArg List.length (headI_dropI (unpairB z).1)
  simp only [List.length_append] at h
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length, List.length_append, List.length_cons, List.length_nil]
    omega

def emit (w : Word) : Word := (unpairB (step^[w.length] (pairB w []))).2

theorem emit_cpt : CPT emit := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 5 step_length
  have hs := cpt_pairB2 cpt_id (cpt_const [])
  have h := cpt_comp (cpt_comp (cpt_pair hs cpt_id) loop) cpt_unpairB2
  exact h

def unitCNF (v : List ℕ) : CNF := v.map (fun i => [(i, true)])

private theorem step_item (i : ℕ) (r a : Word) :
    step (pairB (vcode i ++ r) a) = pairB r (a ++ encodeClause [(i, true)]) := by
  simp [step, unpairB_pairB, dropI_vcode, headI_vcode, sel, vcode_ne_nil, encodeClause,
    encodeLiteral_eq, List.append_assoc]

theorem scan (v : List ℕ) (a : Word) :
    step^[v.length] (pairB (names v) a) = pairB [] (a ++ encodeCNF (unitCNF v)) := by
  induction v generalizing a with
  | nil => simp [names, unitCNF, encodeCNF]
  | cons i v ih =>
    have he : names (i :: v) = vcode i ++ names v := rfl
    rw [he, List.length_cons, Function.iterate_succ_apply, step_item, ih]
    simp [unitCNF, encodeCNF, List.append_assoc]

theorem emit_enc (v : List ℕ) : emit (names v) = encodeCNF (unitCNF v) := by
  have hn : v.length ≤ (names v).length := length_le_flatMap_vcode v
  have hs := scan v []
  have hfix : step (pairB [] (encodeCNF (unitCNF v))) = pairB [] (encodeCNF (unitCNF v)) := by
    simp [step, sel, unpairB_pairB]
  unfold emit
  simp only [List.nil_append] at hs
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, hs, Function.iterate_fixed hfix, unpairB_pairB]

end PEqualNP.Outside.TrueNamesAsUnits
