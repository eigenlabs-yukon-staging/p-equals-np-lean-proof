import PEqualNP.Outside.BooleanParityScan
import PEqualNP.Outside.RecordPairScan

namespace PEqualNP.Outside.AffineRowsMachine

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BooleanParityScan (Word parityWord parityWord_cpt parityWord_correct parity)
open PEqualNP.Outside.RecordPairScan (wire wire_len)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def rowBad (q : Word × Word) : Word :=
  let f := parityWord (q.1.tail, q.2)
  sel (bflag (q.1.headD false)) f (sel f [true] [])

theorem rowBad_cpt : ComputableInPolyTime encodePair (fun x : Word => x) rowBad := by
  have hb := cpt_comp cpt_unpairB1 cpt_firstF
  have hf := cpt_comp (cpt_pair (cpt_tail1 cpt_unpairB1) cpt_unpairB2) parityWord_cpt
  have hc := cpt_sel hb hf (cpt_sel hf (cpt_const [true]) (cpt_const []))
  exact cptl (cpt_comp cpt_pairB hc) (fun _ => by simp [rowBad, unpairB_pairB, bflag])

theorem rowBad_enc (b : Bool) (a w : Word) :
    rowBad (b :: a, w) = bflag (xor b (parity a w false)) := by
  cases b <;> cases h : parity a w false <;> simp [rowBad, parityWord_correct, sel, bflag, h]

def step (z : Word) : Word :=
  let rs := (unpairB z).1
  let v := (unpairB z).2
  let r := unpairB rs
  sel rs z (sel (rowBad (r.1, v)) (pairB r.2 v) z)

theorem step_cpt : CPT step := by
  have hrs := cpt_unpairB1
  have hv := cpt_unpairB2
  have hrow := cpt_unpairB1_1 hrs
  have hrest := cpt_unpairB2_1 hrs
  have hb := cpt_comp (cpt_pair hrow hv) rowBad_cpt
  exact cptl (cpt_sel hrs cpt_id (cpt_sel hb (cpt_pairB2 hrest hv) cpt_id)) (fun _ => rfl)

theorem step_bound (z : Word) : (step z).length ≤ z.length + 1 := by
  have hp := unpairB_length z
  have hq := unpairB_length (unpairB z).1
  simp only [step, sel]
  split
  · omega
  · split
    · rw [pairB_length]
      omega
    · omega

def check (q : Word × Word) : Bool :=
  (unpairB (step^[q.1.length] (pairB q.1 q.2))).1.isEmpty

theorem check_cpt : ComputableInPolyTime encodePair Computability.encodeBool check := by
  obtain ⟨m⟩ := step_cpt
  have hlo := Iter.iter_polyTime step m 1 step_bound
  have hf := cpt_comp (cpt_comp (cpt_pairG cpt_pairB cpt_fst) hlo) cpt_unpairB1
  exact cptl (cpt_comp hf cpt_isEmpty) (fun _ => rfl)

theorem step_row (r rs v : Word) :
    step (pairB (pairB r rs) v) =
      if rowBad (r,v) = [] then pairB rs v else pairB (pairB r rs) v := by
  have hn : pairB r rs ≠ [] := by simp [pairB]
  simp [step, unpairB_pairB, sel, hn]

theorem halt (v : Word) : step (pairB [] v) = pairB [] v := by
  simp [step, unpairB_pairB, sel]

theorem scan (rs : List Word) (v : Word) :
    let z := step^[rs.length] (pairB (wire rs) v)
    step z = z ∧ ((unpairB z).1 = [] ↔ ∀ r ∈ rs, rowBad (r,v) = []) := by
  induction rs with
  | nil => simp [wire, halt, unpairB_pairB]
  | cons r rs ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, wire, step_row]
    by_cases h : rowBad (r,v) = []
    · simpa [h] using ih
    · simp only [h, ite_false]
      have hh : step (pairB (pairB r (wire rs)) v) = pairB (pairB r (wire rs)) v := by
        simp [step_row, h]
      have hn : pairB r (wire rs) ≠ [] := by simp [pairB]
      rw [Function.iterate_fixed hh]
      simp [hh, unpairB_pairB, hn, h]

theorem check_enc (rs : List Word) (v : Word) :
    check (wire rs,v) = true ↔ ∀ r ∈ rs, rowBad (r,v) = [] := by
  have hl := wire_len rs
  have hs := scan rs v
  unfold check
  simp only [List.isEmpty_iff]
  rw [← Nat.sub_add_cancel hl, Function.iterate_add_apply, Function.iterate_fixed hs.1]
  exact hs.2

end PEqualNP.Outside.AffineRowsMachine
