import PEqualNP.Library.Universal.PrimsCPT

/-!
The enumerator and its arithmetic proofs are adapted from the reference
`PEqualNP.Library.Universal.LazyDefs` (Apache-2.0). The separate module lets the
bounded enumeration proof use the counter without the universal interpreter.
-/

namespace PEqualNP.Outside.BoundedEnumeration

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

/-- Transition of the successor transducer: the state is the carry. -/
def succD (carry : Bool) (b : Bool) : Bool × Option Bool :=
  if carry then (b, some (!b)) else (false, some b)

/-- Final output of the successor transducer. -/
def succFin (carry : Bool) : Option Bool := if carry then some false else none

/-- The successor of a bit string in the enumeration of all bit strings, shorter ones first:
leading `true`s become `false`, the first `false` becomes `true`, and a `false` is appended when
there was no `false`. -/
def succB (s : List Bool) : List Bool := fstRun succD succFin true s

/-- The enumeration of all bit strings. -/
def cand (j : ℕ) : List Bool := succB^[j] []

theorem succD_run_false (s : List Bool) : fstRun succD succFin false s = s := by
  induction s with
  | nil => rfl
  | cons b l ih => simp [fstRun, succD, ih]

theorem succB_nil : succB [] = [false] := rfl

theorem succB_false (r : List Bool) : succB (false :: r) = true :: r := by
  simp [succB, fstRun, succD, succD_run_false]

theorem succB_true (r : List Bool) : succB (true :: r) = false :: succB r := by
  simp [succB, fstRun, succD]

/-- The position of a bit string in the enumeration. -/
def idx : List Bool → ℕ
  | [] => 0
  | false :: r => 1 + 2 * idx r
  | true :: r => 2 + 2 * idx r

theorem idx_succB (s : List Bool) : idx (succB s) = idx s + 1 := by
  induction s with
  | nil => rfl
  | cons b r ih =>
    cases b
    · rw [succB_false]; simp [idx]; omega
    · rw [succB_true]; simp [idx, ih]; omega

theorem idx_cand (j : ℕ) : idx (cand j) = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cand, Function.iterate_succ_apply', ← cand, idx_succB, ih]

theorem idx_inj : ∀ s t : List Bool, idx s = idx t → s = t
  | [], [], _ => rfl
  | [], false :: _, h => by simp [idx] at h; omega
  | [], true :: _, h => by simp [idx] at h; omega
  | false :: _, [], h => by simp [idx] at h
  | true :: _, [], h => by simp [idx] at h
  | false :: r, false :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | true :: r, true :: r', h => by
    have := idx_inj r r' (by simp [idx] at h; omega)
    rw [this]
  | false :: _, true :: _, h => by simp [idx] at h; omega
  | true :: _, false :: _, h => by simp [idx] at h; omega

/-- Every bit string occurs in the enumeration, at its position. -/
theorem cand_idx (s : List Bool) : cand (idx s) = s := idx_inj _ _ (idx_cand _)

/-- Shorter strings come first: a string of length `n` has position below `2 ^ (n + 1) - 1`. -/
theorem idx_bound (s : List Bool) : idx s + 2 ≤ 2 ^ (s.length + 1) := by
  induction s with
  | nil => simp [idx]
  | cons b r ih =>
    have e : 2 ^ ((b :: r).length + 1) = 2 * 2 ^ (r.length + 1) := by
      rw [List.length_cons, pow_succ, Nat.mul_comm]
    cases b <;> simp only [idx] <;> omega

theorem idx_lt_of_length_le {s : List Bool} {b : ℕ} (h : s.length ≤ b) :
    idx s + 2 ≤ 2 ^ (b + 1) :=
  (idx_bound s).trans (Nat.pow_le_pow_right (by omega) (by omega))

theorem succB_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) succB :=
  fst_polyTime _ _ _ succD succFin true (fun _ => rfl)

private theorem succD_grows (carry : Bool) (w : List Bool) :
    (fstRun succD succFin carry w).length ≤ w.length + 1 := by
  induction w generalizing carry with
  | nil => cases carry <;> simp [fstRun, succFin]
  | cons b rest ih =>
    have hc := ih b
    have hn := ih false
    cases carry <;> simp [fstRun, succD] <;> omega

theorem succB_grows (w : List Bool) : (succB w).length ≤ w.length + 1 :=
  succD_grows true w

end PEqualNP.Outside.BoundedEnumeration
