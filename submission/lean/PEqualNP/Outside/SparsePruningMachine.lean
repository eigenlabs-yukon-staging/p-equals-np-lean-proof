import PEqualNP.Outside.SparsePruningAlgorithm
import PEqualNP.Outside.SparseRepresentativesMachine

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Word" => List Bool

private def countStep (s : Word) : Word :=
  sel (unpairB s).1 s (pairB (unpairB (unpairB s).1).2 (true :: (unpairB s).2))

private theorem countStep_size (s : Word) : (countStep s).length ≤ s.length + 2 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).1
  unfold countStep
  apply sel_length
  · omega
  · simp only [pairB_length, List.length_cons]; omega

private theorem countStep_polyTime : CPT countStep :=
  bf_cptl (cpt_sel cpt_unpairB1 cpt_id
    (cpt_pairB2 (cpt_unpairB2_1 cpt_unpairB1) (cpt_cons1 true cpt_unpairB2))) (fun _ => rfl)

private theorem count_iter (xs : List Word) :
    ∀ n : Nat, xs.length ≤ n → ∀ c : Word,
      countStep^[n] (pairB (encodeFrontier xs) c) =
        pairB [] (List.replicate xs.length true ++ c) := by
  induction xs with
  | nil =>
    intro n _ c
    have h : countStep (pairB [] c) = pairB [] c := by simp [countStep, unpairB_pairB]
    exact Function.iterate_fixed h n
  | cons x xs ih =>
    intro n hn c
    cases n with
    | zero => simp at hn
    | succ n =>
      have h : countStep (pairB (encodeFrontier (x :: xs)) c) =
          pairB (encodeFrontier xs) (true :: c) := by
        have en : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
        change countStep (pairB (pairB x (encodeFrontier xs)) c) = _
        simp [countStep, unpairB_pairB, sel, en]
      rw [Function.iterate_succ_apply, h, ih n (by simpa using hn)]
      simp [List.replicate_succ', List.append_assoc]

private def frontierCount (s : Word) : Word :=
  (unpairB (countStep^[s.length] (pairB s []))).2

private theorem frontierCount_polyTime : CPT frontierCount :=
  bf_cptl (cpt_unpairB2_1 (cpt_iterGrow countStep_polyTime 2 countStep_size cpt_id
    (cpt_pairB2 cpt_id (cpt_const [])))) (fun _ => rfl)

private theorem frontierCount_spec (xs : List Word) :
    frontierCount (encodeFrontier xs) = List.replicate xs.length true := by
  rw [frontierCount, count_iter xs _ (encodeFrontier_length xs), unpairB_pairB]
  simp

private def lenFlag (a b : Word) : Word := bflag (decide (b.length ≤ a.length))

private theorem lenFlag_polyTime {a b : Word → Word} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => lenFlag (a s) (b s)) :=
  bf_cptl (cpt_bitFlag (cpt_comp (cpt_pair ha hb) LenCmp.lenLE_polyTime)) (fun _ => rfl)

private def pruneMachineStep (f : Word × Word → Word) (s : Word) : Word :=
  let b := (unpairB s).1
  let orig := (unpairB s).2
  let r := representativesMachine f orig
  let kept := (unpairB r).2
  let addPivot := pairB (unpairB orig).1 kept
  let reduced := sel (lenFlag b (unpairB r).1) kept addPivot
  sel orig s (sel (lenFlag (true :: b) (frontierCount orig)) (pairB b reduced) s)

private theorem pruneMachineStep_size (f : Word × Word → Word) (s : Word) :
    (pruneMachineStep f s).length ≤ s.length + 1 := by
  have hd := unpairB_length s
  have hr := representativesMachine_kept_size f (unpairB s).2
  have ho := unpairB_length (unpairB s).2
  unfold pruneMachineStep
  dsimp only
  unfold sel
  split
  · omega
  · rename_i hne
    have hcanon := repack_nonempty_length _ hne
    split
    · split
      · rw [pairB_length]
        omega
      · simp only [pairB_length] at *
        omega
    · omega

private theorem pruneMachineStep_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) : CPT (pruneMachineStep f) := by
  have hb := cpt_unpairB1
  have ho := cpt_unpairB2
  have hr := cpt_comp ho (representativesMachine_polyTime hf)
  have hk := cpt_unpairB2_1 hr
  have hsmall := lenFlag_polyTime (cpt_cons1 true hb) (cpt_comp ho frontierCount_polyTime)
  have hkeep := lenFlag_polyTime hb (cpt_unpairB1_1 hr)
  have hp := cpt_pairB2 (cpt_unpairB1_1 ho) hk
  exact bf_cptl (cpt_sel ho cpt_id (cpt_sel hsmall (cpt_pairB2 hb (cpt_sel hkeep hk hp)) cpt_id))
    (fun _ => rfl)

private theorem reps_agree (f : Word × Word → Word) (p : Word) (xs : List Word) :
    sparseRepresentatives f p xs = sparseListRepresentatives (fun w => f (p,w)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have e : f (p,x) ∈ xs.map (fun w => f (p,w)) ↔ ∃ y ∈ xs, f (p,y) = f (p,x) :=
      List.mem_map
    simp [sparseRepresentatives, sparseListRepresentatives, e, ih]

private theorem pruneMachineStep_spec (f : Word × Word → Word) (b : Nat) (xs : List Word) :
    pruneMachineStep f (pairB (un b) (encodeFrontier xs)) =
      pairB (un b) (encodeFrontier (sparseListStep (fun x y => f (x,y)) b xs)) := by
  cases xs with
  | nil => simp [pruneMachineStep, encodeFrontier, sparseListStep, unpairB_pairB]
  | cons a as =>
    have hne : encodeFrontier (a :: as) ≠ [] := encodeFrontier_cons_ne a as
    have er : encodeFrontier (a :: as) = pairB a (encodeFrontier as) := rfl
    have hr := representativesMachine_spec f a as
    rw [← er] at hr
    by_cases hsmall : as.length ≤ b
    · simp [pruneMachineStep, sparseListStep, unpairB_pairB, sel, hne, lenFlag, bflag,
        frontierCount_spec, un_length, hsmall]
    · let ys := sparseListRepresentatives (fun y => f (a,y)) as
      have hr' : representativesMachine f (encodeFrontier (a :: as)) =
          pairB (List.replicate ys.length true) (encodeFrontier ys) := by
        simpa only [reps_agree] using hr
      have hfirst : (unpairB (encodeFrontier (a :: as))).1 = a := by
        simp [er, unpairB_pairB]
      by_cases h : b < ys.length
      · simp [pruneMachineStep, sparseListStep, unpairB_pairB, sel, hne, lenFlag, bflag,
          frontierCount_spec, un_length, hsmall, hr', hfirst, h, ys]
      · have hle := Nat.le_of_not_gt h
        simp [pruneMachineStep, sparseListStep, unpairB_pairB, sel, hne, lenFlag, bflag,
          frontierCount_spec, un_length, hsmall, hr', hfirst, h, hle, ys]
        rfl

private theorem iterate_spec (f : Word × Word → Word) (b k : Nat) (xs : List Word) :
    (pruneMachineStep f)^[k] (pairB (un b) (encodeFrontier xs)) =
      pairB (un b) (encodeFrontier ((sparseListStep (fun x y => f (x,y)) b)^[k] xs)) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, pruneMachineStep_spec, ih, Function.iterate_succ_apply]

private def pruneMachine (f : Word × Word → Word) (s : Word) : Word :=
  (unpairB ((pruneMachineStep f)^[s.length] s)).2

private theorem pruneMachine_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) : CPT (pruneMachine f) :=
  bf_cptl (cpt_unpairB2_1 (cpt_iterGrow (pruneMachineStep_polyTime hf) 1
    (pruneMachineStep_size f) cpt_id cpt_id)) (fun _ => rfl)

/-- Exact machine realization of sparse disjunctive frontier pruning. The outer word
packs the unary cardinality bound with a self-delimiting list of candidate words. -/
theorem SparsePruningMachine (f : Word × Word → Word)
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    ∃ prune : Word → Word, CPT prune ∧
      ∀ (A B : Language Bool), (∀ x y, f (x,y) ∈ B ↔ x ∈ A ∨ y ∈ A) →
      ∀ (b : Nat) (xs : List Word),
        (∀ a ∈ xs, ∀ z : Finset Word,
          (∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs, f (a,w) = y) → z.card ≤ b) →
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        ∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ b + 1 ∧
          prune (consWord (List.replicate b true) (xs.foldr consWord [])) = ys.foldr consWord [] ∧
          ((∃ x ∈ ys, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  refine ⟨pruneMachine f, pruneMachine_polyTime hf, fun A B hs b xs sparse => ?_⟩
  let w := pairB (un b) (encodeFrontier xs)
  have hk : xs.length ≤ w.length := by
    have h := encodeFrontier_length xs
    simp only [w, pairB_length]
    omega
  let ys := (sparseListStep (fun x y => f (x,y)) b)^[w.length] xs
  obtain ⟨hsub, hsize, hspec⟩ :=
    sparseListRun_correct (fun x y => f (x,y)) b A B hs w.length xs sparse
  have he : pruneMachine f w = encodeFrontier ys := by
    unfold pruneMachine
    simp only [w, iterate_spec, unpairB_pairB, ys]
  exact ⟨ys, hsub, by simpa [ys, Nat.sub_eq_zero_of_le hk] using hsize, he, hspec⟩

end PEqualNP.Outside
