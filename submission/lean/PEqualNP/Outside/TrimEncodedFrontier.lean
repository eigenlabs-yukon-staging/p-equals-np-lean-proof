import PEqualNP.Outside.FrontierExpansionMachine

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private def takeStep (s : Word) : Word :=
  let fuel := (unpairB s).1
  let rem := (unpairB s).2
  let todo := (unpairB rem).1
  let accum := (unpairB rem).2
  let next := pairB fuel.tail (pairB (unpairB todo).2 (accum ++ pairB (unpairB todo).1 []))
  sel fuel s (sel todo s next)

private theorem takeStep_cpt : CPT takeStep := by
  have hf := cpt_unpairB1
  have hr := cpt_unpairB2
  have ht := cpt_unpairB1_1 hr
  have ha := cpt_unpairB2_1 hr
  have hx := cpt_unpairB1_1 ht
  have hxs := cpt_unpairB2_1 ht
  have hn := cpt_pairB2 (cpt_comp hf cpt_tail)
    (cpt_pairB2 hxs (cpt_app2 ha (cpt_pairB2 hx (cpt_const []))))
  exact bf_cptl (cpt_sel hf cpt_id (cpt_sel ht cpt_id hn)) (fun _ => rfl)

private theorem takeStep_size (s : Word) : (takeStep s).length ≤ s.length + 3 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  have ht := unpairB_length (unpairB (unpairB s).2).1
  unfold takeStep
  dsimp only
  apply sel_length
  · omega
  · apply sel_length
    · omega
    · simp only [pairB_length, List.length_append, List.length_tail, List.length_nil]
      omega

private def taking (fuel : Word) (xs ys : List Word) : Word :=
  pairB fuel (pairB (encodeFrontier xs) (encodeFrontier ys))

private theorem takeRun (fuel : Word) (xs ys : List Word) (k : Nat) (hk : fuel.length ≤ k) :
    (unpairB (unpairB (takeStep^[k] (taking fuel xs ys))).2).2 =
      encodeFrontier (ys ++ xs.take fuel.length) := by
  induction fuel generalizing xs ys k with
  | nil =>
    have hs : takeStep (taking [] xs ys) = taking [] xs ys := by
      simp [takeStep, taking, unpairB_pairB]
    rw [Function.iterate_fixed hs k]
    simp [taking, unpairB_pairB]
  | cons b fuel ih =>
    cases xs with
    | nil =>
      have hs : takeStep (taking (b::fuel) [] ys) = taking (b::fuel) [] ys := by
        simp [takeStep, taking, unpairB_pairB, encodeFrontier]
      rw [Function.iterate_fixed hs k]
      simp [taking, unpairB_pairB]
    | cons x xs =>
      cases k with
      | zero => simp at hk
      | succ k =>
        have hstep : takeStep (taking (b::fuel) (x::xs) ys) = taking fuel xs (ys++[x]) := by
          have hne : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
          change takeStep (pairB (b::fuel) (pairB (pairB x (encodeFrontier xs)) (encodeFrontier ys))) = _
          have he : encodeFrontier [x] = pairB x [] := rfl
          simp [takeStep, taking, unpairB_pairB, hne, sel, encodeFrontier_append_words, he]
        rw [Function.iterate_succ_apply, hstep, ih xs (ys++[x]) k (by simpa using hk)]
        simp [List.append_assoc]

private def takeRaw (s : Word) : Word :=
  let n := (unpairB s).1
  let xs := (unpairB s).2
  (unpairB (unpairB (takeStep^[n.length] (pairB n (pairB xs [])))).2).2

private theorem takeRaw_cpt : CPT takeRaw :=
  bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow takeStep_cpt 3 takeStep_size
    cpt_unpairB1 (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const []))))))
    (fun _ => rfl)

private theorem takeRaw_spec (n : Word) (xs : List Word) :
    takeRaw (pairB n (encodeFrontier xs)) = encodeFrontier (xs.take n.length) := by
  unfold takeRaw
  simp only [unpairB_pairB]
  simpa [taking, encodeFrontier] using takeRun n xs [] n.length le_rfl

private def dropRaw (s : Word) : Word :=
  (fun w : Word => (unpairB w).2)^[(unpairB s).1.length] (unpairB s).2

private theorem dropRaw_cpt : CPT dropRaw :=
  cpt_iterLen cpt_unpairB2 (fun s => by have h := unpairB_length s; omega)
    cpt_unpairB1 cpt_unpairB2

private theorem dropRaw_spec (n : Word) (xs : List Word) :
    dropRaw (pairB n (encodeFrontier xs)) = encodeFrontier (xs.drop n.length) := by
  unfold dropRaw
  simp only [unpairB_pairB]
  generalize n.length = k
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      have e : (unpairB (encodeFrontier [])).2 = [] := rfl
      rw [e]
      simpa [encodeFrontier] using ih []
    | cons x xs =>
      have e : (unpairB (encodeFrontier (x::xs))).2 = encodeFrontier xs := unpairB_pairB _ _ ▸ rfl
      simpa only [e, List.drop_succ_cons] using ih xs

private noncomputable def countEncoded (s : Word) : Word := expandFrontier (fun _ => [false]) 1 s

private theorem countEncoded_cpt : CPT countEncoded :=
  expandFrontier_polyTime (cpt_const [false]) 1

private theorem countEncoded_length (xs : List Word) :
    (countEncoded (encodeFrontier xs)).length = xs.length := by
  have hc : ∀ x : Word, [false] = encodeFrontier ([[]] : List Word) := fun _ => rfl
  have h := expandFrontier_spec (fun _ => ([[]] : List Word))
    (fun _ => [false]) hc 1 (by simp) xs
  change countEncoded (encodeFrontier xs) = _ at h
  rw [h]
  clear h hc
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (pairB [] (encodeFrontier (xs.flatMap (fun _ => [[]])))).length = xs.length + 1
    simp only [pairB_length, List.length_nil, Nat.mul_zero, Nat.zero_add, ih]

private noncomputable def excess (s : Word) : Word :=
  List.drop ((unpairB s).1.length + 1) (countEncoded (unpairB s).2)

private theorem iterTail (n : Nat) (w : Word) :
    (fun x : Word => x.tail)^[n] w = w.drop n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases w <;> simp

private theorem excess_cpt : CPT excess :=
  bf_cptl (cpt_iterLen cpt_tail (fun w => by simp only [List.length_tail]; omega)
    (cpt_cons1 true cpt_unpairB1) (cpt_comp cpt_unpairB2 countEncoded_cpt))
    (fun s => by simp [excess, iterTail])

private noncomputable def trimRaw (s : Word) : Word :=
  let m := (unpairB s).1
  let k := excess s
  let cut := sel (bflag (decide (k.length ≤ m.length))) k m
  takeRaw s ++ dropRaw (pairB cut (unpairB s).2)

private theorem trimRaw_cpt : CPT trimRaw := by
  have hle := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 excess_cpt) LenCmp.lenLE_polyTime)
  have hcut := cpt_sel hle excess_cpt cpt_unpairB1
  exact bf_cptl (cpt_app2 takeRaw_cpt (cpt_comp (cpt_pairB2 hcut cpt_unpairB2) dropRaw_cpt))
    (fun _ => rfl)

private theorem trimRaw_spec (m : Word) (xs : List Word) :
    trimRaw (pairB m (encodeFrontier xs)) =
      encodeFrontier (xs.take m.length ++ xs.drop (max m.length (xs.length - (m.length+1)))) := by
  let k := excess (pairB m (encodeFrontier xs))
  have he : k.length = xs.length - (m.length+1) := by
    simp [k, excess, unpairB_pairB, countEncoded_length]
  unfold trimRaw
  simp only [unpairB_pairB, takeRaw_spec, dropRaw_spec, encodeFrontier_append_words]
  change _ ++ encodeFrontier (xs.drop (sel (bflag (decide (k.length ≤ m.length))) k m).length) = _
  by_cases hm : k.length ≤ m.length
  · rw [← he, max_eq_left hm]
    simp [hm,bflag]
  · rw [← he, max_eq_right (Nat.le_of_not_ge hm)]
    simp [hm,bflag]

theorem TrimEncodedFrontier :
    ∃ run : Word × Word → Word,
      ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (m : Word) (xs : List Word),
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (m, xs.foldr consWord []) =
          (xs.take m.length ++ xs.drop (max m.length (xs.length - (m.length+1)))).foldr consWord [] := by
  exact ⟨fun p => trimRaw (pairB p.1 p.2), cpt_comp cpt_pairB trimRaw_cpt, trimRaw_spec⟩

end PEqualNP.Outside
