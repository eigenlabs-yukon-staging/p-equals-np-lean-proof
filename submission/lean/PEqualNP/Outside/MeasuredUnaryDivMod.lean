import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.L055
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

private def step (s : List Bool) : List Bool :=
  let d := (unpairB s).1
  let r := (unpairB (unpairB s).2).1
  let q := (unpairB (unpairB s).2).2
  if d = [] then s
  else if d.length ≤ r.length then pairB d (pairB (r.drop d.length) (true :: q))
  else s

private theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
  have hd := cpt_unpairB1
  have hr := cpt_unpairB1_1 cpt_unpairB2
  have hq := cpt_unpairB2_1 cpt_unpairB2
  have hdrop := cpt_iterLen cpt_tail (fun w => by simp) hd hr
  have hf := cpt_bitFlag (cpt_comp (cpt_pair hr hd) LenCmp.lenLE_polyTime)
  have hnext := cpt_pairB2 hd (cpt_pairB2 hdrop (cpt_cons1 true hq))
  refine cptE (cpt_sel hd cpt_id (cpt_sel hf cpt_id hnext)) (fun s => ?_)
  have he (w : List Bool) (n : ℕ) : List.tail^[n] w = w.drop n := by
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, List.drop_tail]
  simp only [sel, step, he]
  split
  · rfl
  · by_cases h : (unpairB s).1.length ≤ (unpairB (unpairB s).2).1.length <;> simp [h]

private theorem step_length (s : List Bool) : (step s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 : ((unpairB (unpairB s).2).1.drop (unpairB s).1.length).length ≤
      (unpairB (unpairB s).2).1.length := by simp
  dsimp only [step]
  split
  · omega
  · split
    · simp only [pairB_length, List.length_cons]
      omega
    · omega

private theorem step_canonical (d r q : List Bool) :
    step (pairB d (pairB r q)) =
      if d = [] then pairB d (pairB r q)
      else if d.length ≤ r.length then pairB d (pairB (r.drop d.length) (true :: q))
      else pairB d (pairB r q) := by
  simp only [step, unpairB_pairB]

private theorem iter_fixed (s : List Bool) (h : step s = s) (n : ℕ) :
    step^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, h, ih]

private theorem run (d r q : List Bool) (n : ℕ) (hn : r.length ≤ n) :
    (step^[n] (pairB d (pairB r q))) =
      pairB d (pairB (r.drop (r.length - r.length % d.length))
        (List.replicate (r.length / d.length) true ++ q)) := by
  induction n generalizing r q with
  | zero =>
      have hr : r = [] := List.length_eq_zero_iff.mp (by omega)
      subst r
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, step_canonical]
      by_cases hd : d = []
      · subst d
        have hfix := iter_fixed (pairB [] (pairB r q)) (by simp [step_canonical]) n
        simpa using hfix
      · have hdpos : 0 < d.length := by
          cases d <;> simp_all
        by_cases h : d.length ≤ r.length
        · have hr : (r.drop d.length).length ≤ n := by simp [List.length_drop]; omega
          rw [ite_eq_right hd, ite_eq_left h, ih _ _ hr, List.length_drop]
          rw [Nat.div_eq_sub_div hdpos h, Nat.mod_eq_sub_mod h]
          have hmod := Nat.mod_le (r.length - d.length) d.length
          have hadd : d.length + (r.length - d.length - (r.length - d.length) % d.length) =
              r.length - (r.length - d.length) % d.length := by omega
          rw [List.drop_drop, hadd, List.replicate_succ']
          simp [List.append_assoc]
        · have hfix := iter_fixed (pairB d (pairB r q)) (by simp [step_canonical, hd, h]) n
          rw [ite_eq_right hd, ite_eq_right h, hfix, Nat.div_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
          simp

set_option maxHeartbeats 1000000 in
/-- Unary division and remainder, with division by zero returning quotient zero and
the original numerator as remainder. All input bit values are ignored. -/
theorem MeasuredUnaryDivMod :
    ∃ divide : List Bool × List Bool → List Bool × List Bool,
      ComputableInPolyTime encodePair encodePair divide ∧
      ∀ a b : List Bool,
        divide (a,b) = (List.replicate (a.length / b.length) true,
          List.replicate (a.length % b.length) true) := by
  let iter := fun s => step^[(unpairB s).1.length]
    (pairB (unpairB s).2 (pairB (unpairB s).1 []))
  let decoded := fun s => unpairB (unpairB (iter s)).2
  let divide := fun p : List Bool × List Bool =>
    let r := decoded (pairB p.1 p.2)
    (r.2, List.replicate r.1.length true)
  have hi : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) iter :=
    cpt_iterGrow cpt_step 3 step_length cpt_unpairB1
      (cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const [])))
  have hb := cpt_comp cpt_pairB (cpt_unpairB2_1 hi)
  have hquot := cpt_comp hb cpt_unpairB2
  have hrem := cpt_comp hb cpt_unpairB1
  have hnorm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => List.replicate x.length true) := by
    simpa using L055 Polynomial.X
  have hd : ComputableInPolyTime encodePair encodePair divide :=
    cpt_pairG hquot (cpt_comp hrem hnorm)
  refine ⟨divide, hd, fun a b => ?_⟩
  simp only [divide, decoded, iter, unpairB_pairB, run _ _ _ _ le_rfl, List.append_nil]
  simp only [List.length_drop]
  have := Nat.mod_le a.length b.length
  congr
  omega

end PEqualNP.Outside
