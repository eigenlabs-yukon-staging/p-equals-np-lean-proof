import PEqualNP.Outside.RecordPairScan
import PEqualNP.Library.Universal.Padding

namespace PEqualNP.Outside.AllRecordTest

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire wire_len)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (T : Word × Word → Bool) (z : Word) : Word :=
  let rs := (unpairB z).1
  let w := (unpairB z).2
  let pair := unpairB rs
  sel rs z (sel (bflag (T (pair.1,w))) z (pairB pair.2 w))

theorem step_cpt (T : Word × Word → Bool)
    (hT : ComputableInPolyTime encodePair Computability.encodeBool T) : CPT (step T) := by
  have hr := cpt_unpairB1
  have hw := cpt_unpairB2
  have hf := cpt_bitFlag (cpt_comp (cpt_pair (cpt_unpairB1_1 hr) hw) hT)
  exact cptl (cpt_sel hr cpt_id (cpt_sel hf cpt_id (cpt_pairB2 (cpt_unpairB2_1 hr) hw)))
    (fun _ => by simp [step, bflag])

theorem step_size (T : Word × Word → Bool) (z : Word) :
    (step T z).length ≤ z.length + 1 := by
  have hp := unpairB_length z
  have hq := unpairB_length (unpairB z).1
  simp only [step, sel]
  split
  · omega
  · split
    · omega
    · rw [pairB_length]
      omega

def check (T : Word × Word → Bool) (q : Word × Word) : Bool :=
  (unpairB ((step T)^[q.1.length] (pairB q.1 q.2))).1.isEmpty

theorem check_cpt (T : Word × Word → Bool)
    (hT : ComputableInPolyTime encodePair Computability.encodeBool T) :
    ComputableInPolyTime encodePair Computability.encodeBool (check T) := by
  obtain ⟨m⟩ := step_cpt T hT
  have hlo := Iter.iter_polyTime (step T) m 1 (step_size T)
  have hr := cpt_comp (cpt_comp (cpt_pairG cpt_pairB cpt_fst) hlo) cpt_unpairB1
  exact cptl (cpt_comp hr cpt_isEmpty) (fun _ => rfl)

theorem scan (T : Word × Word → Bool) (rs : List Word) (w : Word) :
    let z := (step T)^[rs.length] (pairB (wire rs) w)
    step T z = z ∧ ((unpairB z).1 = [] ↔ ∀ r ∈ rs, T (r,w) = true) := by
  induction rs with
  | nil => simp [step, wire, sel, unpairB_pairB]
  | cons a as ih =>
    have hn : pairB a (wire as) ≠ [] := by simp [pairB]
    have hs : step T (pairB (pairB a (wire as)) w) =
        if T (a,w) then pairB (wire as) w else pairB (pairB a (wire as)) w := by
      cases h : T (a,w) <;> simp [step, sel, unpairB_pairB, hn, bflag, h]
    simp only [List.length_cons, Function.iterate_succ_apply, wire, hs]
    cases ht : T (a,w)
    · try simp only [ht, ite_false]
      have hf : step T (pairB (pairB a (wire as)) w) = pairB (pairB a (wire as)) w := by
        simp [hs, ht]
      simp [Function.iterate_fixed hf, hf, unpairB_pairB, hn, ht]
    · simpa [ht] using ih

theorem check_enc (T : Word × Word → Bool) (rs : List Word) (w : Word) :
    check T (wire rs,w) = true ↔ ∀ r ∈ rs, T (r,w) = true := by
  have hs := scan T rs w
  have hl := wire_len rs
  unfold check
  simp only [List.isEmpty_iff]
  rw [← Nat.sub_add_cancel hl, Function.iterate_add_apply, Function.iterate_fixed hs.1]
  exact hs.2

end PEqualNP.Outside.AllRecordTest
