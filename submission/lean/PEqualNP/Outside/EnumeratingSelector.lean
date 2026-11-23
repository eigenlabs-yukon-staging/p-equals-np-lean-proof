import PEqualNP.Outside.BoundedEnumeration
import PEqualNP.Outside.PrefixDecideHelpers

namespace PEqualNP.Outside.EnumeratingSelector

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.BoundedEnumeration PEqualNP.Outside.PrefixDecideHelpers

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def next (test : Word → Bool) (w : Word) : Word :=
  if test w then w else succB w

theorem next_accepts (test : Word → Bool) (w : Word) (j n : ℕ)
    (hj : j ≤ n) (hw : test (succB^[j] w) = true) :
    test ((next test)^[n] w) = true := by
  induction j generalizing n w with
  | zero =>
    have ht : test w = true := hw
    have hf : next test w = w := by simp [next, ht]
    simpa only [Function.iterate_fixed hf] using ht
  | succ j ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases ht : test w = true
      · have hf : next test w = w := by simp [next, ht]
        simpa only [Function.iterate_fixed hf] using ht
      · rw [Function.iterate_succ_apply]
        have hf : next test w = succB w := by simp [next, ht]
        rw [hf]
        exact ih _ _ (by omega) (by simpa only [Function.iterate_succ_apply] using hw)

def step (done : Word → Bool) (z : Word) : Word :=
  let x := (unpairB z).1
  let w := (unpairB z).2
  pairB x (next (fun w => done (pairB x w)) w)

theorem step_cpt {done : Word → Bool}
    (hd : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool done) :
    CPT (step done) := by
  have reset := cpt_pairB2 cpt_unpairB1 cpt_unpairB2
  have advance := cpt_pairB2 cpt_unpairB1 (cpt_comp cpt_unpairB2 succB_cpt)
  have flag := cpt_bitFlag (cpt_comp reset hd)
  have hc := cpt_sel flag advance reset
  have eq : (fun z => sel (if done (pairB (unpairB z).1 (unpairB z).2) then [true] else [])
      (pairB (unpairB z).1 (succB (unpairB z).2)) (pairB (unpairB z).1 (unpairB z).2)) =
      step done := by
    funext z
    cases hd' : done (pairB (unpairB z).1 (unpairB z).2) <;> simp [step, next, sel, hd']
  exact eq ▸ hc

theorem step_grows (done : Word → Bool) (z : Word) :
    (step done z).length ≤ z.length + 2 := by
  simp only [step, pairB_length]
  have h := unpairB_length z
  unfold next
  split
  · omega
  · have hg := succB_grows (unpairB z).2
    omega

theorem iterate_packed (done : Word → Bool) (x w : Word) (n : ℕ) :
    (step done)^[n] (pairB x w) =
      pairB x ((next (fun w => done (pairB x w)))^[n] w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [step, unpairB_pairB]

theorem select_bounded (R : Rel) (p q : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) :
    ∃ s : Word → Word, CPT s ∧
      ∀ x : Word, (∃ w : Word, good R p x w ∧ idx w ≤ q.eval x.length) → good R p x (s x) := by
  obtain ⟨verify, hv, hc⟩ := hR
  let done : Word → Bool := fun z =>
    decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)
  let g := step done
  have hcpt : CPT g := step_cpt (cpt_test verify p hc)
  let s := fun x : Word => (unpairB (g^[q.eval x.length] (pairB x []))).2
  refine ⟨s, ?_, ?_⟩
  · exact clocked_selector hcpt q (step_grows done)
  · rintro x ⟨w, hw, hidx⟩
    have hd' : ∀ w : Word, done (pairB x w) = true ↔ good R p x w := by
      intro w
      simp only [done, unpairB_pairB, good, Bool.and_eq_true, decide_eq_true_eq, hv]
    change good R p x (unpairB ((step done)^[q.eval x.length] (pairB x []))).2
    rw [iterate_packed, unpairB_pairB, ← hd']
    apply next_accepts (fun w => done (pairB x w)) [] (idx w) _ hidx
    change done (pairB x (cand (idx w))) = true
    rw [cand_idx]
    exact (hd' w).mpr hw

end PEqualNP.Outside.EnumeratingSelector
