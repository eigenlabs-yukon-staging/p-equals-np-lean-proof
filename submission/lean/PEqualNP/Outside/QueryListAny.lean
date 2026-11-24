import PEqualNP.Outside.RecordPairScan
import PEqualNP.Library.Universal.Padding

namespace PEqualNP.Outside.QueryListAny

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire wire_len)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (test : Word → Bool) (w : Word) : Word :=
  sel w w (sel (bflag (test (unpairB w).1)) (unpairB w).2 w)

theorem step_cpt (test : Word → Bool)
    (ht : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool test) :
    CPT (step test) :=
  cptl (cpt_sel cpt_id cpt_id (cpt_sel (cpt_bitFlag (cpt_comp cpt_unpairB1 ht)) cpt_unpairB2 cpt_id))
    (fun w => by simp [step, bflag])

theorem step_bound (test : Word → Bool) (w : Word) : (step test w).length ≤ w.length + 0 := by
  have h := unpairB_length w
  unfold step sel
  split
  · omega
  · split <;> omega

def endState (test : Word → Bool) (w : Word) : Word := (step test)^[w.length] w

theorem endState_cpt (test : Word → Bool)
    (ht : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool test) :
    CPT (endState test) := by
  obtain ⟨m⟩ := step_cpt test ht
  exact cptl (cpt_comp (cpt_pair cpt_id cpt_id) (Iter.iter_polyTime (step test) m 0 (step_bound test)))
    (fun _ => rfl)

def answer (test : Word → Bool) (w : Word) : Bool := (sel (endState test w) [true] []).isEmpty

theorem answer_cpt (test : Word → Bool)
    (ht : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool test) :
    ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (answer test) :=
  cptl (cpt_comp (cpt_sel (endState_cpt test ht) (cpt_const [true]) (cpt_const [])) cpt_isEmpty)
    (fun _ => rfl)

theorem step_cons (test : Word → Bool) (q r : Word) :
    step test (pairB q r) = if test q then pairB q r else r := by
  have hn : pairB q r ≠ [] := by simp [pairB]
  cases h : test q <;> simp [step, unpairB_pairB, sel, bflag, hn, h]

theorem scan (test : Word → Bool) (qs : List Word) :
    let z := (step test)^[qs.length] (wire qs)
    step test z = z ∧ (z ≠ [] ↔ ∃ q ∈ qs, test q = true) := by
  induction qs with
  | nil => simp [wire, step, sel]
  | cons q qs ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, wire, step_cons]
    cases h : test q
    · simpa [h] using ih
    · have hh : step test (pairB q (wire qs)) = pairB q (wire qs) := by simp [step_cons, h]
      have hn : pairB q (wire qs) ≠ [] := by simp [pairB]
      simp only [h, ite_true, Function.iterate_fixed hh]
      exact ⟨hh, fun _ => ⟨q, by simp, h⟩, fun _ => hn⟩

theorem answer_enc (test : Word → Bool) (qs : List Word) :
    answer test (wire qs) = true ↔ ∃ q ∈ qs, test q = true := by
  have hu := wire_len qs
  have hscan := scan test qs
  unfold answer endState
  rw [← Nat.sub_add_cancel hu, Function.iterate_add_apply, Function.iterate_fixed hscan.1]
  refine Iff.trans ?_ hscan.2
  by_cases h : (step test)^[qs.length] (wire qs) = [] <;> simp [sel, h]

theorem wire_fold (qs : List Word) :
    wire qs = qs.foldr (fun v rest => List.replicate v.length true ++ false :: (v ++ rest)) [] := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [wire, pairB, un, ih]

end PEqualNP.Outside.QueryListAny
