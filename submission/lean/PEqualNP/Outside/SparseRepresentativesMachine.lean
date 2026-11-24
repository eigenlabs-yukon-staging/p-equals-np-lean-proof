import PEqualNP.Outside.PolynomialImageMembership

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Word" => List Bool

def encodeFrontier (xs : List Word) : Word := xs.foldr pairB []

private theorem encodeFrontier_append (xs ys : List Word) :
    encodeFrontier (xs ++ ys) = encodeFrontier xs ++ encodeFrontier ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeFrontier, List.cons_append, List.foldr_cons, pairB, List.append_assoc,
      List.cons_append] at *
    rw [ih]

theorem encodeFrontier_length (xs : List Word) : xs.length ≤ (encodeFrontier xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change xs.length + 1 ≤ (pairB x (encodeFrontier xs)).length
    rw [pairB_length]
    omega

theorem encodeFrontier_cons_ne (x : Word) (xs : List Word) : encodeFrontier (x :: xs) ≠ [] := by
  intro h
  have hh := encodeFrontier_length (x :: xs)
  simpa [h] using hh

def sparseRepresentatives (f : Word × Word → Word) (p : Word) : List Word → List Word
  | [] => []
  | x :: xs => if ∃ y ∈ xs, f (p,y) = f (p,x) then
      sparseRepresentatives f p xs else x :: sparseRepresentatives f p xs

private def repStep (f : Word × Word → Word) (s : Word) : Word :=
  let p := (unpairB s).1
  let r := (unpairB s).2
  let todo := (unpairB r).1
  let a := (unpairB r).2
  let count := (unpairB a).1
  let kept := (unpairB a).2
  let x := (unpairB todo).1
  let xs := (unpairB todo).2
  let matched := bflag (imageLookup f (pairB p (pairB (f (p,x)) xs)))
  let keep := pairB (true :: count) (kept ++ pairB x [])
  let next := pairB p (pairB xs (sel matched keep a))
  sel todo s next

private theorem repStep_size (f : Word × Word → Word) (s : Word) :
    (repStep f s).length ≤ s.length + 6 := by
  have hs := unpairB_length s
  have hr := unpairB_length (unpairB s).2
  have ha := unpairB_length (unpairB (unpairB s).2).2
  have ht := unpairB_length (unpairB (unpairB s).2).1
  unfold repStep
  dsimp only
  apply sel_length
  · omega
  · rw [pairB_length, pairB_length]
    unfold sel
    split
    · simp only [pairB_length, List.length_append, List.length_cons, List.length_nil]
      omega
    · omega

theorem repack_nonempty_length (s : Word) (hne : s ≠ []) :
    (pairB (unpairB s).1 (unpairB s).2).length ≤ s.length := by
  have hsum := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := s))
  rw [List.length_append] at hsum
  cases h : s.dropWhile id with
  | nil =>
    simp [pairB_length, unpairB, h]
    exact List.length_pos_iff.mpr hne
  | cons b t =>
    rw [h, List.length_cons] at hsum
    simp only [pairB_length, unpairB, h, List.tail_cons, List.length_take, List.length_drop]
    omega

private def repSize (s : Word) : Nat :=
  let r := (unpairB s).2
  (unpairB r).1.length + (unpairB (unpairB r).2).2.length

private theorem repSize_step (f : Word × Word → Word) (s : Word) :
    repSize (repStep f s) ≤ repSize s := by
  unfold repStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · rename_i hne
    have hs := repack_nonempty_length _ hne
    simp only [repSize, unpairB_pairB]
    split
    · simp only [unpairB_pairB, List.length_append, pairB_length, List.length_nil] at *
      omega
    · have hz := unpairB_length (unpairB (unpairB s).2).1
      omega

private theorem repStep_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    CPT (repStep f) := by
  have hp := cpt_unpairB1
  have hr := cpt_unpairB2
  have ht := cpt_unpairB1_1 hr
  have ha := cpt_unpairB2_1 hr
  have hc := cpt_unpairB1_1 ha
  have hk := cpt_unpairB2_1 ha
  have hx := cpt_unpairB1_1 ht
  have hxs := cpt_unpairB2_1 ht
  have hi := cpt_comp (cpt_pair hp hx) hf
  have hm := cpt_bitFlag (cpt_comp (cpt_pairB2 hp (cpt_pairB2 hi hxs))
    (imageLookup_polyTime hf))
  have hkeep := cpt_pairB2 (cpt_cons1 true hc) (cpt_app2 hk (cpt_pairB2 hx (cpt_const [])))
  exact bf_cptl (cpt_sel ht cpt_id (cpt_pairB2 hp (cpt_pairB2 hxs (cpt_sel hm hkeep ha))))
    (fun _ => rfl)

private def repState (p : Word) (todo kept : List Word) (count : Word) : Word :=
  pairB p (pairB (encodeFrontier todo) (pairB count (encodeFrontier kept)))

private theorem repStep_nil (f : Word × Word → Word) (p : Word) (ys : List Word) (c : Word) :
    repStep f (repState p [] ys c) = repState p [] ys c := by
  simp [repStep, repState, encodeFrontier, unpairB_pairB]

private theorem repStep_cons (f : Word × Word → Word) (p x : Word) (xs ys : List Word) (c : Word) :
    repStep f (repState p (x :: xs) ys c) =
      if ∃ y ∈ xs, f (p,y) = f (p,x) then repState p xs ys c
      else repState p xs (ys ++ [x]) (true :: c) := by
  have ec : encodeFrontier (x :: xs) = pairB x (encodeFrontier xs) := rfl
  have en : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
  have hmatch := imageLookup_spec f p (f (p,x)) xs
  change imageLookup f (pairB p (pairB (f (p,x)) (encodeFrontier xs))) = true ↔ _ at hmatch
  by_cases h : ∃ y ∈ xs, f (p,y) = f (p,x)
  · have ht := hmatch.mpr h
    simp [repStep, repState, ec, unpairB_pairB, en, sel, bflag, h, ht]
  · have hf : imageLookup f (pairB p (pairB (f (p,x)) (encodeFrontier xs))) = false := by
      cases hval : imageLookup f (pairB p (pairB (f (p,x)) (encodeFrontier xs)))
      · rfl
      · exact False.elim (h (hmatch.mp hval))
    have hsingle : encodeFrontier [x] = pairB x [] := rfl
    simp [repStep, repState, ec, unpairB_pairB, en, sel, bflag, h, hf,
      encodeFrontier_append, hsingle]

private theorem rep_iter (f : Word × Word → Word) (p : Word) (xs : List Word) :
    ∀ (n : Nat), xs.length ≤ n → ∀ (ys : List Word) (c : Word),
      (repStep f)^[n] (repState p xs ys c) =
        repState p [] (ys ++ sparseRepresentatives f p xs)
          (List.replicate (sparseRepresentatives f p xs).length true ++ c) := by
  induction xs with
  | nil =>
    intro n _ ys c
    simpa [sparseRepresentatives] using Function.iterate_fixed (repStep_nil f p ys c) n
  | cons x xs ih =>
    intro n hn ys c
    cases n with
    | zero => simp at hn
    | succ n =>
      have hn' : xs.length ≤ n := by simpa using hn
      rw [Function.iterate_succ_apply, repStep_cons]
      by_cases h : ∃ y ∈ xs, f (p,y) = f (p,x)
      · simpa [sparseRepresentatives, h] using ih n hn' ys c
      · rw [if_neg h, ih n hn' (ys ++ [x]) (true :: c)]
        simp only [sparseRepresentatives, h, ite_false, List.length_cons]
        simp [List.replicate_succ', List.append_assoc]

def representativesMachine (f : Word × Word → Word) (s : Word) : Word :=
  let init := pairB (unpairB s).1 (pairB (unpairB s).2 (pairB [] []))
  (unpairB (unpairB ((repStep f)^[s.length] init)).2).2

theorem representativesMachine_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    CPT (representativesMachine f) := by
  have h := cpt_iterGrow (repStep_polyTime hf) 6 (repStep_size f) cpt_id
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const (pairB [] []))))
  exact bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 h)) (fun _ => rfl)

theorem representativesMachine_kept_size (f : Word × Word → Word) (s : Word) :
    (unpairB (representativesMachine f s)).2.length ≤ (unpairB s).2.length := by
  let init := pairB (unpairB s).1 (pairB (unpairB s).2 (pairB [] []))
  have his : ∀ n, repSize ((repStep f)^[n] init) ≤ repSize init := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (repSize_step f _).trans ih
  have hinit : repSize init = (unpairB s).2.length := by
    simp [repSize, init, unpairB_pairB]
  have hn := (his s.length).trans_eq hinit
  change (unpairB (representativesMachine f s)).2.length ≤ _
  have hh : repSize ((repStep f)^[s.length] init) =
      ((unpairB (unpairB ((repStep f)^[s.length] init)).2).1).length +
        (unpairB (representativesMachine f s)).2.length := rfl
  rw [hh] at hn
  omega

theorem representativesMachine_spec (f : Word × Word → Word) (p : Word) (xs : List Word) :
    representativesMachine f (pairB p (encodeFrontier xs)) =
      pairB (List.replicate (sparseRepresentatives f p xs).length true)
        (encodeFrontier (sparseRepresentatives f p xs)) := by
  have hn : xs.length ≤ (pairB p (encodeFrontier xs)).length := by
    rw [pairB_length]
    have := encodeFrontier_length xs
    omega
  have init : pairB p (pairB (encodeFrontier xs) (pairB [] [])) = repState p xs [] [] := rfl
  simp only [representativesMachine, unpairB_pairB]
  rw [init, rep_iter f p xs _ hn]
  simp [repState, unpairB_pairB]

end PEqualNP.Outside
