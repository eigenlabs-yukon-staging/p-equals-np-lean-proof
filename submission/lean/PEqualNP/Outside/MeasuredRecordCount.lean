import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

private def pack (words : List (List Bool)) : List Bool := words.foldr pairB []

private def step (s : List Bool) : List Bool :=
  let rest := (unpairB s).1
  if rest = [] then s
  else pairB (unpairB rest).2 (true :: (unpairB s).2)

private theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step :=
  cpt_sel cpt_unpairB1 cpt_id
    (cpt_pairB2 (cpt_unpairB2_1 cpt_unpairB1) (cpt_cons1 true cpt_unpairB2))

private theorem step_length (s : List Bool) : (step s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  dsimp only [step]
  split
  · omega
  · simp only [pairB_length, List.length_cons]
    omega

private theorem pack_nonempty (w : List Bool) (ws : List (List Bool)) :
    pack (w :: ws) ≠ [] := by
  change pairB w (pack ws) ≠ []
  intro h
  have hlen := pairB_length w (pack ws)
  rw [h] at hlen
  simp at hlen

private theorem pack_length (ws : List (List Bool)) : ws.length ≤ (pack ws).length := by
  induction ws with
  | nil => simp [pack]
  | cons w ws ih =>
      change ws.length + 1 ≤ (pairB w (pack ws)).length
      rw [pairB_length]
      omega

private theorem run (words : List (List Bool)) (acc : List Bool) (n : ℕ)
    (hn : words.length ≤ n) :
    step^[n] (pairB (pack words) acc) = pairB [] (List.replicate words.length true ++ acc) := by
  induction n generalizing words acc with
  | zero =>
      have h : words = [] := List.length_eq_zero_iff.mp (by omega)
      subst words
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases words with
      | nil =>
          have e : step (pairB (pack []) acc) = pairB (pack []) acc := by
            simp [step, pack, unpairB_pairB]
          rw [e]
          exact ih [] acc (by simp)
      | cons w ws =>
          have e : step (pairB (pack (w :: ws)) acc) = pairB (pack ws) (true :: acc) := by
            have he := pack_nonempty w ws
            have hpack : pack (w :: ws) = pairB w (pack ws) := rfl
            simp only [step, unpairB_pairB, ite_eq_right he]
            rw [hpack, unpairB_pairB]
          rw [e, ih _ _ (by simpa using hn), List.length_cons, List.replicate_succ']
          simp [List.append_assoc]

/-- Return a unary count for any word in the canonical nested record encoding. -/
theorem MeasuredRecordCount :
    ∃ count : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) count ∧
      ∀ words : List (List Bool),
        count (words.foldr (fun word rest =>
          List.replicate word.length true ++ false :: (word ++ rest)) []) =
          List.replicate words.length true := by
  let count := fun s => (unpairB (step^[s.length] (pairB s []))).2
  have hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) count :=
    cpt_unpairB2_1 (cpt_iterGrow cpt_step 2 step_length cpt_id (cpt_pairB2 cpt_id (cpt_const [])))
  refine ⟨count, hc, fun ws => ?_⟩
  change count (pack ws) = _
  dsimp only [count]
  rw [run _ _ _ (pack_length ws), unpairB_pairB, List.append_nil]

end PEqualNP.Outside
