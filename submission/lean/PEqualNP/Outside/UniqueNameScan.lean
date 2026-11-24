import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.UniqueNameScan

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (z : Word) : Word :=
  let r := (unpairB z).1
  let s := (unpairB z).2
  let h := headI r
  sel r z (pairB (dropI r) (sel (bflag (memB h s)) (s ++ h) s))

theorem step_cpt : CPT step := by
  have hh := cpt_comp cpt_unpairB1 cpt_headI
  have hs := cpt_sel (cpt_memB hh cpt_unpairB2) (cpt_app2 cpt_unpairB2 hh) cpt_unpairB2
  exact cptl (cpt_sel cpt_unpairB1 cpt_id (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropI) hs))
    (fun _ => rfl)

theorem step_growth (z : Word) : (step z).length ≤ z.length + 1 := by
  have h := unpairB_length z
  have ht := congrArg List.length (headI_dropI (unpairB z).1)
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length]
    split
    · simp only [List.length_append]
      omega
    · omega

def unique (x : Word) : Word :=
  (unpairB (step^[x.length] (pairB x []))).2

theorem unique_cpt : CPT unique := by
  obtain ⟨c⟩ := step_cpt
  have h := cpt_comp (cpt_comp (cpt_pair (cpt_pairB2 cpt_id (cpt_const [])) cpt_id)
    (Iter.iter_polyTime step c 1 step_growth)) cpt_unpairB2
  exact h

def scan (s : List ℕ) : List ℕ → List ℕ
  | [] => s
  | v :: vs => scan (if v ∈ s then s else s ++ [v]) vs

theorem mem_scan (i : ℕ) (s vs : List ℕ) : i ∈ scan s vs ↔ i ∈ s ∨ i ∈ vs := by
  induction vs generalizing s with
  | nil => simp [scan]
  | cons v vs ih =>
    by_cases h : v ∈ s
    · simp only [scan, h, ite_true, ih, List.mem_cons]
      grind
    · simp only [scan, h, ite_false, ih, List.mem_cons, List.mem_append, List.mem_singleton]
      grind

theorem scan_nodup (s vs : List ℕ) (hs : s.Nodup) : (scan s vs).Nodup := by
  induction vs generalizing s with
  | nil => exact hs
  | cons v vs ih =>
    by_cases h : v ∈ s
    · simpa [scan, h] using ih s hs
    · simp only [scan, h, ite_false]
      apply ih
      exact (by
        simp [List.nodup_append, hs]
        intro i hi e
        exact h (e ▸ hi))

theorem scan_count (vs : List ℕ) : (scan [] vs).length = vs.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (scan_nodup [] vs (by simp))]
  congr 1
  ext i
  simp [mem_scan]

theorem step_var (v : ℕ) (r : Word) (s : List ℕ) :
    step (pairB (vcode v ++ r) (s.flatMap vcode)) =
      pairB r ((if v ∈ s then s else s ++ [v]).flatMap vcode) := by
  have hm : memB (vcode v) (s.flatMap vcode) = decide (v ∈ s) :=
    Bool.eq_iff_iff.mpr ((asg_codes s v).trans (by simp))
  by_cases h : v ∈ s <;> simp [step, sel, unpairB_pairB, vcode_ne_nil, dropI_vcode,
    headI_vcode, hm, h, bflag, List.flatMap_append]

theorem run_enc (vs : List ℕ) (s : List ℕ) :
    step^[vs.length] (pairB (vs.flatMap vcode) (s.flatMap vcode)) =
      pairB [] ((scan s vs).flatMap vcode) := by
  induction vs generalizing s with
  | nil => simp [scan]
  | cons v vs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons, step_var]
    exact ih _

theorem unique_enc (vs : List ℕ) :
    unique (vs.flatMap vcode) = ((scan [] vs).flatMap vcode) := by
  have hlen := length_le_flatMap_vcode vs
  have hfix : step (pairB [] ((scan [] vs).flatMap vcode)) =
      pairB [] ((scan [] vs).flatMap vcode) := by simp [step, sel, unpairB_pairB]
  unfold unique
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, ← List.flatMap_nil (f := vcode),
    run_enc, Function.iterate_fixed hfix, unpairB_pairB]

end PEqualNP.Outside.UniqueNameScan
