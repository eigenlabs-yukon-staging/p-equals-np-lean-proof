import PEqualNP.Outside.MaxClauseWidthMachine
import PEqualNP.Outside.BackdoorPathCore

namespace PEqualNP.Outside.WidthDigitClock

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.MaxClauseWidthMachine (Word clock clock_cpt clock_enc maxWidth)
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (cut cut_cpt cut_eq)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

/- The unary binary-size implementation is from the pinned Universal.LazyDefs.
   The time proof below exposes its local wrapper for the width-based interpreter. -/
theorem half_cpt : CPT half :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

theorem log_step_cpt : CPT lgStep :=
  cptl (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_cons1 true cpt_unpairB1) (cpt_comp cpt_unpairB2 half_cpt)))
    (fun _ => rfl)

theorem log_step_length (s : Word) : (lgStep s).length ≤ s.length + 2 := by
  have h := unpairB_length s
  unfold lgStep sel
  split
  · omega
  · rename_i hn
    have hlen : 1 ≤ (unpairB s).2.length := by
      cases hb : (unpairB s).2 with
      | nil => exact absurd hb hn
      | cons b l => simp
    rw [pairB_length, half_eq, un_length, List.length_cons]
    omega

theorem lgU_cpt : CPT lgU :=
  cptl (cpt_unpairB1_1 (cpt_iterGrow log_step_cpt 2 log_step_length cpt_id
    (cpt_pairB2 (cpt_const []) cpt_id))) (fun _ => rfl)

def digitClock (x : Word) : Word := lgU (clock x).tail

theorem digitClock_cpt : CPT digitClock := by
  have h := cpt_comp (cpt_tail1 clock_cpt) lgU_cpt
  exact h

theorem digitClock_enc (φ : CNF) :
    digitClock (encodeCNF φ) = un (maxWidth φ - 1).size := by
  have htail (n : ℕ) : (un n).tail = un (n - 1) := by
    cases n <;> simp [un, List.replicate_succ]
  rw [digitClock, clock_enc, htail, lgU_un]

def skip (pad w : Word) : Word := (unpairB (mulU pad [true] ++ false :: w)).2

theorem skip_eq (pad w : Word) : skip pad w = w.drop pad.length := by
  have h1 : (mulU pad [true] ++ false :: w).takeWhile id = un pad.length := by
    simp [mulU, un]
  have h2 : (mulU pad [true] ++ false :: w).dropWhile id = false :: w := by
    simp [mulU, un]
  simp [skip, unpairB, h1, h2, un]

theorem skip_cpt {p w : Word → Word} (hp : CPT p) (hw : CPT w) : CPT (fun z => skip (p z) (w z)) :=
  cpt_unpairB2_1 (cpt_app2 (cpt_mulU2 hp (cpt_const [true])) (cpt_cons1 false hw))

theorem maxWidth_bound (φ : CNF) : IsKCNF (maxWidth φ) φ := by
  induction φ with
  | nil => simp [IsKCNF]
  | cons c cs ih =>
    intro a hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_max_left _ _
    · exact (ih _ hm).trans (le_max_right _ _)

theorem maxWidth_fold (φ : CNF) :
    maxWidth φ = φ.foldr (fun c n => max c.length n) 0 := by
  induction φ with
  | nil => rfl
  | cons c cs ih => simp [maxWidth, ih]

theorem fixedBits_width (φ : CNF) : IsKCNF (2 ^ (maxWidth φ - 1).size) φ := by
  intro c hc
  have h := Nat.lt_size_self (maxWidth φ - 1)
  have hm := maxWidth_bound φ c hc
  omega

end PEqualNP.Outside.WidthDigitClock
