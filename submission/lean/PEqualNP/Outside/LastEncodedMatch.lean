import PEqualNP.Outside.FrontierFilterByParameter

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

private def lastStep (s : Word) : Word :=
  let remaining := (unpairB s).2
  sel remaining s (pairB (true :: (unpairB remaining).1) (unpairB remaining).2)

private theorem lastStep_cpt : CPT lastStep :=
  bf_cptl (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_cons1 true (cpt_unpairB1_1 cpt_unpairB2))
      (cpt_unpairB2_1 cpt_unpairB2))) (fun _ => rfl)

private theorem lastStep_size (s : Word) : (lastStep s).length ≤ s.length + 3 := by
  have h := unpairB_length s
  have hr := unpairB_length (unpairB s).2
  unfold lastStep
  dsimp only
  unfold sel
  split
  · omega
  · simp only [pairB_length, List.length_cons]
    omega

private def lastValue (previous : Word) (xs : List Word) : Word :=
  match xs.getLast? with
  | none => previous
  | some x => true :: x

private theorem last_iter (previous : Word) (xs : List Word) (n : Nat) (h : xs.length ≤ n) :
    lastStep^[n] (pairB previous (encodeFrontier xs)) = pairB (lastValue previous xs) [] := by
  induction n generalizing xs previous with
  | zero =>
    have he : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      have he : lastStep (pairB previous (encodeFrontier [])) = pairB previous [] := by
        simp [lastStep, encodeFrontier, unpairB_pairB]
      rw [he]
      exact ih previous [] (by simp)
    | cons x xs =>
      have hne := encodeFrontier_cons_ne x xs
      have he : lastStep (pairB previous (encodeFrontier (x::xs))) =
          pairB (true :: x) (encodeFrontier xs) := by
        have hp : encodeFrontier (x::xs) = pairB x (encodeFrontier xs) := rfl
        rw [hp] at hne
        simp [lastStep, unpairB_pairB, sel, hne, hp]
      rw [he, ih (true :: x) xs (by simpa using h)]
      cases xs with
      | nil => rfl
      | cons y ys =>
        simp only [lastValue, List.getLast?_cons_cons]
        cases hopt : (y :: ys).getLast? with
        | none => simp at hopt
        | some z => rfl

private def lastPacked (s : Word) : Word :=
  (unpairB (lastStep^[s.length] (pairB [] s))).1

private theorem lastPacked_cpt : CPT lastPacked :=
  cpt_unpairB1_1 (cpt_iterGrow lastStep_cpt 3 lastStep_size cpt_id
    (cpt_pairB2 (cpt_const []) cpt_id))

private theorem lastPacked_spec (xs : List Word) :
    lastPacked (encodeFrontier xs) = lastValue [] xs := by
  unfold lastPacked
  rw [last_iter [] xs _ (encodeFrontier_length xs), unpairB_pairB]

/-- Select the last encoded record satisfying a measured parameterized predicate,
with a leading true tag on success and an empty output on failure. -/
theorem LastEncodedMatch (pred : Word × Word → Bool)
    (hp : ComputableInPolyTime encodePair Computability.encodeBool pred) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (a : Word) (xs : List Word),
        let pack := fun x y : Word => List.replicate x.length true ++ false :: (x ++ y)
        run (a,xs.foldr pack []) =
          ((xs.filter (fun x => pred (a,x))).getLast?.map (List.cons true)).getD [] := by
  obtain ⟨filter, hf, hs⟩ := FrontierFilterByParameter pred hp
  refine ⟨fun p => lastPacked (filter p), cpt_comp hf lastPacked_cpt, fun a xs => ?_⟩
  have he : filter (a,encodeFrontier xs) =
      encodeFrontier (xs.filter (fun x => pred (a,x))) := hs a xs
  change lastPacked (filter (a,encodeFrontier xs)) = _
  rw [he,lastPacked_spec]
  unfold lastValue
  cases (xs.filter (fun x => pred (a,x))).getLast? <;> rfl

end PEqualNP.Outside
