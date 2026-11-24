import PEqualNP.Outside.WidthDigitClock

namespace PEqualNP.Outside.NameDigitClock

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.WidthDigitClock (lgU_cpt)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (z : Word) : Word :=
  let r := (unpairB z).1
  sel r z (pairB (dropI r) (true :: (unpairB z).2))

theorem step_cpt : CPT step :=
  cptl (cpt_sel cpt_unpairB1 cpt_id
    (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropI) (cpt_cons1 true cpt_unpairB2))) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 2 := by
  have h := unpairB_length z
  have hdrop := dropI_length (unpairB z).1
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length, List.length_cons]
    omega

def count (w : Word) : Word := (unpairB (step^[w.length] (pairB w []))).2

theorem count_cpt : CPT count := by
  unfold count
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 2 step_length
  have h := cpt_comp (cpt_comp (cpt_pair (cpt_pairB2 cpt_id (cpt_const [])) cpt_id) loop) cpt_unpairB2
  exact h

theorem scan (xs : List ℕ) (n : ℕ) :
    step^[xs.length] (pairB (xs.flatMap vcode) (un n)) = pairB [] (un (n + xs.length)) := by
  induction xs generalizing n with
  | nil => simp
  | cons i xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons]
    have h : step (pairB (vcode i ++ xs.flatMap vcode) (un n)) =
        pairB (xs.flatMap vcode) (un (n + 1)) := by
      simp [step, sel, unpairB_pairB, vcode_ne_nil, dropI_vcode, un, List.replicate_succ]
    rw [h, ih]
    congr 2
    omega

theorem count_codes (xs : List ℕ) : count (xs.flatMap vcode) = un xs.length := by
  have h := scan xs 0
  simp only [un_zero, Nat.zero_add] at h
  have hn := length_le_flatMap_vcode xs
  have hfix : step (pairB [] (un xs.length)) = pairB [] (un xs.length) := by
    simp [step, sel, unpairB_pairB]
  rw [count, ← Nat.sub_add_cancel hn, Function.iterate_add_apply, h, Function.iterate_fixed hfix,
    unpairB_pairB]

def clock (w : Word) : Word := lgU (count w).tail

theorem clock_cpt : CPT clock := by
  unfold clock
  exact cpt_comp (cpt_tail1 count_cpt) lgU_cpt

theorem clock_codes (xs : List ℕ) : clock (xs.flatMap vcode) = un (xs.length - 1).size := by
  have htail (n : ℕ) : (un n).tail = un (n - 1) := by
    cases n <;> simp [un, List.replicate_succ]
  rw [clock, count_codes, htail, lgU_un]

end PEqualNP.Outside.NameDigitClock
