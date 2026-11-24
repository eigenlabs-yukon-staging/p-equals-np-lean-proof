import PEqualNP.Defs

namespace PEqualNP.Outside.PrefixIteration

abbrev Word := List Bool

def advance (done canExtend : Word → Bool) (pre : Word) : Word :=
  if done pre then pre
  else if canExtend (pre ++ [false]) then pre ++ [false]
  else pre ++ [true]

theorem advance_length (done canExtend : Word → Bool) (pre : Word) :
    (advance done canExtend pre).length ≤ pre.length + 1 := by
  unfold advance
  split
  · omega
  · split <;> simp

theorem iterate_correct
    (done canExtend : Word → Bool) (good : Word → Prop)
    (hd : ∀ pre, done pre = true ↔ good pre)
    (he : ∀ pre, canExtend pre = true ↔ ∃ s : Word, good (pre ++ s))
    (k : ℕ) (hlen : ∀ w, good w → w.length ≤ k)
    (n : ℕ) (pre : Word) (hbudget : k ≤ pre.length + n)
    (hex : ∃ s : Word, good (pre ++ s)) :
    good ((advance done canExtend)^[n] pre) := by
  induction n generalizing pre with
  | zero =>
      obtain ⟨s, hs⟩ := hex
      have hz := hlen _ hs
      simp only [List.length_append, Nat.add_zero] at hz hbudget
      have hnil : s = [] := List.length_eq_zero_iff.mp (by omega)
      simpa [hnil] using hs
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      unfold advance
      split
      · rename_i hyes
        have hstep : advance done canExtend pre = pre := by simp [advance, hyes]
        change good ((advance done canExtend)^[n] pre)
        rw [Function.iterate_fixed hstep]
        exact (hd pre).mp hyes
      · rename_i hdno
        split
        · rename_i h
          exact ih _ (by simpa [List.length_append] using (show k ≤ pre.length + 1 + n by omega))
            ((he _).mp h)
        · rename_i hfalse
          apply ih
          · simpa [List.length_append] using (show k ≤ pre.length + 1 + n by omega)
          · obtain ⟨s, hs⟩ := hex
            cases s with
            | nil => exact False.elim (hdno ((hd pre).mpr (by simpa using hs)))
            | cons b s =>
              cases b
              · exact False.elim (hfalse ((he _).mpr ⟨s, by simpa using hs⟩))
              · exact ⟨s, by simpa using hs⟩

end PEqualNP.Outside.PrefixIteration
