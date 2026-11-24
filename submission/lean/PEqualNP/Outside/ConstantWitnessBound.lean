import PEqualNP.Outside.FiniteWitnessSearch

namespace PEqualNP.Outside

open PEqualNP.Library

private def wordsThrough : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: ((wordsThrough n).map (false :: ·) ++ (wordsThrough n).map (true :: ·))

private theorem mem_wordsThrough (n : Nat) (w : List Bool) :
    w ∈ wordsThrough n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => cases w <;> simp [wordsThrough]
  | succ n ih =>
    cases w with
    | nil => simp [wordsThrough]
    | cons b w =>
      cases b <;> simp [wordsThrough, ih, Nat.succ_le_succ_iff]

/-- Uniform in the witness bound as a proposition. Each fixed bound yields its own
polynomial-time machine, whose description may grow with the bound. -/
theorem ConstantWitnessBound (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) (n : Nat) :
    ({x : List Bool | ∃ w : List Bool, w.length ≤ n ∧ (x, w) ∈ R} : Language Bool) ∈ P := by
  simpa only [mem_wordsThrough] using FiniteWitnessSearch R hR (wordsThrough n)

end PEqualNP.Outside
