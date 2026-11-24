import PEqualNP.Outside.AllFormulaNames
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Universal.Padding
import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.ModelTrueCount

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.AllFormulaNames (collect collect_cpt collect_enc distinct)
open PEqualNP.Outside.CnfRestrictionSemantics (names)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def rest (z : Word) : Word := (unpairB z).1
def witness (z : Word) : Word := (unpairB (unpairB z).2).1
def count (z : Word) : Word := (unpairB (unpairB z).2).2
def pack (r w a : Word) : Word := pairB r (pairB w a)

def step (z : Word) : Word :=
  let r := rest z
  let w := witness z
  let a := count z
  let f := bflag (memB (headI r) w)
  sel r z (pack (dropI r) w (sel f a (true :: a)))

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have hw : CPT witness := cpt_unpairB1_1 cpt_unpairB2
  have ha : CPT count := cpt_unpairB2_1 cpt_unpairB2
  have hf := cpt_memB (cpt_comp hr cpt_headI) hw
  have hv := cpt_sel hf ha (cpt_cons1 true ha)
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 (cpt_comp hr cpt_dropI) (cpt_pairB2 hw hv))) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 3 := by
  have h := unpairB_length z
  have hw := unpairB_length (unpairB z).2
  have hd := dropI_length (rest z)
  have hv : (sel (bflag (memB (headI (rest z)) (witness z))) (count z) (true :: count z)).length ≤
      (count z).length + 1 := by
    unfold sel
    split <;> simp
  change (sel (rest z) z (pack (dropI (rest z)) (witness z)
    (sel (bflag (memB (headI (rest z)) (witness z))) (count z) (true :: count z)))).length ≤ _
  unfold sel at hv ⊢
  split
  · omega
  · simp only [pack, pairB_length, rest, witness, count] at hd hv ⊢
    omega

def run (q : Word × Word) : Word :=
  count (step^[q.1.length] (pack q.1 q.2 []))

theorem run_cpt : ComputableInPolyTime encodePair (fun x : Word => x) run := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 3 step_length
  have hp := cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 q.2 []) :=
    cptl hp (fun _ => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_comp (cpt_pairG hs cpt_fst) loop) (cpt_unpairB2_1 cpt_unpairB2)
  exact h

theorem step_name (i : ℕ) (r w : Word) (acc : ℕ) :
    step (pack (vcode i ++ r) w (un acc)) =
      pack r w (un (acc + if asg w i then 1 else 0)) := by
  cases h : memB (vcode i) w <;>
    simp [step, pack, rest, witness, count, unpairB_pairB, sel, headI_vcode, dropI_vcode,
      vcode_ne_nil, bflag, asg, h, un, List.replicate_succ]

theorem scan (vs : List ℕ) (w : Word) (acc : ℕ) :
    step^[vs.length] (pack (names vs) w (un acc)) =
      pack [] w (un (acc + (vs.filter (asg w)).length)) := by
  induction vs generalizing acc with
  | nil => simp [names]
  | cons i vs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have he : names (i :: vs) = vcode i ++ names vs := rfl
    rw [he, step_name, ih]
    cases h : asg w i <;> simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem run_names (vs : List ℕ) (w : Word) :
    run (names vs, w) = un ((vs.filter (asg w)).length) := by
  have hn : vs.length ≤ (names vs).length := length_le_flatMap_vcode vs
  have he := scan vs w 0
  have hf : step (pack [] w (un (vs.filter (asg w)).length)) =
      pack [] w (un (vs.filter (asg w)).length) := by
    simp [step, pack, rest, unpairB_pairB, sel]
  simp only [un_zero, Nat.zero_add] at he
  change count (step^[(names vs).length] (pack (names vs) w [])) = _
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, he, Function.iterate_fixed hf]
  simp [count, pack, unpairB_pairB]

def modelWeight (q : Word × Word) : Word := run (collect q.1, q.2)

theorem modelWeight_cpt : ComputableInPolyTime encodePair (fun x : Word => x) modelWeight := by
  have h := cpt_comp (cpt_pairG (cpt_comp cpt_fst collect_cpt) cpt_snd) run_cpt
  exact h

theorem modelWeight_enc (φ : CNF) (w : Word) :
    modelWeight (encodeCNF φ, w) = un (((distinct φ).filter (asg w)).length) := by
  unfold modelWeight
  simp only [collect_enc, run_names]

end PEqualNP.Outside.ModelTrueCount
