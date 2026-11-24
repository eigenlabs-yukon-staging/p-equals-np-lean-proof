import PEqualNP.Outside.EnumeratingSelector

namespace PEqualNP.Outside.MinimalRankSelector

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.BoundedEnumeration
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.EnumeratingSelector (next step step_cpt step_grows iterate_packed)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

theorem next_least (test : Word → Bool) (w : Word) (j n : ℕ)
    (hj : j ≤ n) (hw : test (succB^[j] w) = true) :
    ∃ k ≤ j, (next test)^[n] w = succB^[k] w ∧ test (succB^[k] w) = true ∧
      ∀ i < k, test (succB^[i] w) = false := by
  induction j generalizing n w with
  | zero =>
    have ht : test w = true := hw
    have hf : next test w = w := by simp [next, ht]
    exact ⟨0, le_rfl, Function.iterate_fixed hf _, ht, by simp⟩
  | succ j ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases ht : test w with
      | true =>
        have hf : next test w = w := by simp [next, ht]
        exact ⟨0, Nat.zero_le _, Function.iterate_fixed hf _, ht, by simp⟩
      | false =>
        have hf : next test w = succB w := by simp [next, ht]
        have htail : test (succB^[j] (succB w)) = true := by
          simpa only [Function.iterate_succ_apply] using hw
        obtain ⟨k, hk, he, ha, hn⟩ := ih (succB w) n (by omega) htail
        refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
        · rw [Function.iterate_succ_apply, hf, he, Function.iterate_succ_apply]
        · simpa only [Function.iterate_succ_apply] using ha
        · intro i hi
          cases i with
          | zero => exact ht
          | succ i => simpa only [Function.iterate_succ_apply] using hn i (by omega)

theorem pow_lower (w : Word) : 2 ^ w.length ≤ idx w + 1 := by
  induction w with
  | nil => simp [idx]
  | cons b w ih =>
    have he : 2 ^ (b :: w).length = 2 * 2 ^ w.length := by
      rw [List.length_cons, pow_succ, Nat.mul_comm]
    rw [he]
    cases b <;> simp only [idx] <;> omega

theorem length_le_of_idx_le {a b : Word} (h : idx a ≤ idx b) : a.length ≤ b.length := by
  by_contra! hn
  have hpow : 2 ^ (b.length + 1) ≤ 2 ^ a.length := Nat.pow_le_pow_right (by decide) (by omega)
  have hlo := pow_lower a
  have hhi := idx_bound b
  omega

theorem select_least (R : Rel) (p q : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) :
    ∃ s : Word → Word, CPT s ∧
      ∀ x : Word, (∃ w : Word, good R p x w ∧ idx w ≤ q.eval x.length) →
        good R p x (s x) ∧ ∀ w, good R p x w → idx (s x) ≤ idx w := by
  obtain ⟨verify, hv, hc⟩ := hR
  let done : Word → Bool := fun z =>
    decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)
  let g := step done
  have hcpt : CPT g := step_cpt (cpt_test verify p hc)
  let s := fun x : Word => (unpairB (g^[q.eval x.length] (pairB x []))).2
  refine ⟨s, clocked_selector hcpt q (step_grows done), ?_⟩
  rintro x ⟨w, hw, hidx⟩
  let test : Word → Bool := fun w => done (pairB x w)
  have he (w : Word) : test w = true ↔ good R p x w := by
    simp only [test, done, unpairB_pairB, good, Bool.and_eq_true, decide_eq_true_eq, hv]
  have hw' : test (cand (idx w)) = true := by
    rw [cand_idx]
    exact (he w).mpr hw
  obtain ⟨k, hk, hscan, hgood, hleast⟩ := next_least test [] (idx w) _ hidx hw'
  have hs : s x = cand k := by
    change (unpairB ((step done)^[q.eval x.length] (pairB x []))).2 = _
    rw [iterate_packed, unpairB_pairB, hscan]
    rfl
  refine ⟨(he _).mp (hs.symm ▸ hgood), ?_⟩
  intro u hu
  rw [hs, idx_cand]
  by_contra! hn
  have hfalse := hleast (idx u) hn
  change test (cand (idx u)) = false at hfalse
  rw [cand_idx] at hfalse
  rw [(he u).mpr hu] at hfalse
  contradiction

end PEqualNP.Outside.MinimalRankSelector
