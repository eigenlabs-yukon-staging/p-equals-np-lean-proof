import PEqualNP.Outside.BoundedBitRepair

namespace PEqualNP.Outside

open PEqualNP.Library

private def applyFlips (is : List ℕ) (word : List Bool) : List Bool :=
  is.foldl (fun word i => word.modify i Bool.not) word

private theorem applyFlips_succ (is : List ℕ) (b : Bool) (word : List Bool) :
    applyFlips (is.map Nat.succ) (b :: word) = b :: applyFlips is word := by
  induction is generalizing word with
  | nil => rfl
  | cons i is ih =>
      exact ih (word.modify i Bool.not)

private theorem repair_schedule (word target : List Bool) (hs : word.length = target.length) :
    ∃ is : List ℕ,
      is.length = (List.zipWith (fun a b => decide (a ≠ b)) word target).count true ∧
      applyFlips is word = target := by
  induction word generalizing target with
  | nil =>
      cases target with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons b rest => simp at hs
  | cons a word ih =>
      cases target with
      | nil => simp at hs
      | cons b target =>
          obtain ⟨is, hlen, hcalc⟩ := ih target (by simpa using hs)
          by_cases h : a = b
          · subst b
            refine ⟨is.map Nat.succ, ?_, ?_⟩
            · simpa using hlen
            · rw [applyFlips_succ, hcalc]
          · have hn : (!a) = b := by cases a <;> cases b <;> simp_all
            refine ⟨0 :: is.map Nat.succ, ?_, ?_⟩
            · simp [h, hlen]
            · change applyFlips (is.map Nat.succ) ((!a) :: word) = b :: target
              rw [applyFlips_succ, hcalc, hn]

private theorem modify_past_end (word : List Bool) : word.modify word.length Bool.not = word := by
  induction word with
  | nil => rfl
  | cons b word ih => exact congrArg (b :: ·) ih

private theorem applyFlips_pad (word : List Bool) (n : ℕ) :
    applyFlips (List.replicate n word.length) word = word := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change applyFlips (List.replicate n word.length) (word.modify word.length Bool.not) = word
    rwa [modify_past_end]

/-- A bounded-Hamming-error predictor suffices for a deterministic verifier-based decider. -/
theorem HammingCoveredVerifier
    (L : Language Bool) (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (predict : List Bool → List Bool)
    (hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) predict)
    (k : ℕ)
    (complete : ∀ x : List Bool, x ∈ L → ∃ w : List Bool,
      (x, w) ∈ R ∧ w.length = (predict x).length ∧
      (List.zipWith (fun a b => decide (a ≠ b)) (predict x) w).count true ≤ k)
    (sound : ∀ x w : List Bool, (x, w) ∈ R → x ∈ L) :
    L ∈ P := by
  have h := BoundedBitRepair R hR predict hp k
  have heq : L = {x : List Bool | ∃ is : List ℕ, is.length = k ∧ (x, applyFlips is (predict x)) ∈ R} := by
    ext x
    change x ∈ L ↔ ∃ is : List ℕ, is.length = k ∧ (x, applyFlips is (predict x)) ∈ R
    constructor
    · intro hx
      obtain ⟨w, hw, hlen, hdiff⟩ := complete x hx
      obtain ⟨is, hi, hcalc⟩ := repair_schedule (predict x) w hlen.symm
      refine ⟨is ++ List.replicate (k - is.length) w.length, ?_, ?_⟩
      · simp only [List.length_append, List.length_replicate]
        omega
      · have hfold : applyFlips (is ++ List.replicate (k - is.length) w.length) (predict x) =
            applyFlips (List.replicate (k - is.length) w.length) (applyFlips is (predict x)) := by
          simp [applyFlips, List.foldl_append]
        rw [hfold, hcalc, applyFlips_pad]
        exact hw
    · rintro ⟨is, _, hi⟩
      exact sound x _ hi
  rw [heq]
  exact h

end PEqualNP.Outside
