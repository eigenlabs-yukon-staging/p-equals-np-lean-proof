import PEqualNP.Outside.SparseConjunctiveBoundary
import PEqualNP.Outside.CoSparseQueryFrontier
import PEqualNP.Library.Machines.ReduceNP

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private def boundaryStep (g : Word → Word) (s : Word) : Word :=
  let cap := (unpairB s).1
  let x₀ := (unpairB s).2
  let todo := (unpairB x₀).1
  let x₁ := (unpairB x₀).2
  let seen := (unpairB x₁).1
  let x₂ := (unpairB x₁).2
  let fuel := (unpairB x₂).1
  let x₃ := (unpairB x₂).2
  let prev := (unpairB x₃).1
  let kept := (unpairB x₃).2
  let x := (unpairB todo).1
  let xs := (unpairB todo).2
  let q := g x
  let small := bflag (decide (q.length ≤ cap.length))
  let fresh := bflag (freshQuery seen q)
  let nextPrev := pairB x []
  let skip := pairB seen (pairB fuel (pairB nextPrev kept))
  let add := pairB (seen ++ q) (pairB fuel.tail (pairB nextPrev (kept ++ prev)))
  let next := pairB cap (pairB xs (sel small skip (sel fresh skip add)))
  sel todo s (sel fuel s next)

private def boundaryMeasure (s : Word) : Nat := 2 * (unpairB s).1.length + 7

private theorem boundaryMeasure_step (g : Word → Word) (s : Word) :
    boundaryMeasure (boundaryStep g s) ≤ boundaryMeasure s := by
  unfold boundaryStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · simp [boundaryMeasure, unpairB_pairB]

private theorem boundaryStep_size (g : Word → Word) (s : Word) :
    (boundaryStep g s).length ≤ s.length + boundaryMeasure s := by
  have h₀ := unpairB_length s
  have h₁ := unpairB_length (unpairB s).2
  have h₂ := unpairB_length (unpairB (unpairB s).2).2
  have h₃ := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
  have h₄ := unpairB_length (unpairB (unpairB (unpairB (unpairB s).2).2).2).2
  have ht := unpairB_length (unpairB (unpairB s).2).1
  unfold boundaryStep boundaryMeasure
  dsimp only
  unfold sel
  split
  · omega
  · split
    · omega
    · simp only [pairB_length]
      split
      · simp only [pairB_length, List.length_nil]; omega
      · rename_i hne
        have hl := (not_congr (bflag_eq_nil _)).mp hne
        simp only [Bool.not_eq_false, decide_eq_true_eq] at hl
        split
        · simp only [pairB_length, List.length_nil]; omega
        · simp only [pairB_length, List.length_append, List.length_tail, List.length_nil]
          omega

private theorem boundaryStep_cpt {g : Word → Word} (hg : CPT g) : CPT (boundaryStep g) := by
  have hcap := cpt_unpairB1
  have h₀ := cpt_unpairB2
  have ht := cpt_unpairB1_1 h₀
  have h₁ := cpt_unpairB2_1 h₀
  have hs := cpt_unpairB1_1 h₁
  have h₂ := cpt_unpairB2_1 h₁
  have hf := cpt_unpairB1_1 h₂
  have h₃ := cpt_unpairB2_1 h₂
  have hp := cpt_unpairB1_1 h₃
  have hk := cpt_unpairB2_1 h₃
  have hx := cpt_unpairB1_1 ht
  have hq := cpt_comp hx hg
  have hsmall := cpt_bitFlag (cpt_comp (cpt_pair hcap hq) LenCmp.lenLE_polyTime)
  have hfresh := cpt_bitFlag (freshQuery_cpt hs hq)
  have hn := cpt_pairB2 hx (cpt_const [])
  have hskip := cpt_pairB2 hs (cpt_pairB2 hf (cpt_pairB2 hn hk))
  have hadd := cpt_pairB2 (cpt_app2 hs hq)
    (cpt_pairB2 (cpt_comp hf cpt_tail) (cpt_pairB2 hn (cpt_app2 hk hp)))
  have hnext := cpt_pairB2 hcap (cpt_pairB2 (cpt_unpairB2_1 ht)
    (cpt_sel hsmall hskip (cpt_sel hfresh hskip hadd)))
  exact bf_cptl (cpt_sel ht cpt_id (cpt_sel hf cpt_id hnext)) (fun _ => rfl)

private def boundaryState (cap : Word) (todo seen : List Word) (fuel : Nat)
    (prev : Option Word) (kept : List Word) : Word :=
  pairB cap (pairB (encodeFrontier todo) (pairB (encodeFrontier seen)
    (pairB (un fuel) (pairB (encodeFrontier prev.toList) (encodeFrontier kept)))))

private def boundaryRead (s : Word) : Word :=
  let d := (unpairB (unpairB (unpairB s).2).2).2
  let fuel := (unpairB d).1
  let out := (unpairB d).2
  let prev := (unpairB out).1
  let kept := (unpairB out).2
  sel fuel kept (kept ++ prev)

private theorem boundaryRead_cpt : CPT boundaryRead := by
  have h := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have hfuel := cpt_unpairB1_1 h
  have hout := cpt_unpairB2_1 h
  have hp := cpt_unpairB1_1 hout
  have hk := cpt_unpairB2_1 hout
  exact bf_cptl (cpt_sel hfuel hk (cpt_app2 hk hp)) (fun _ => rfl)

private theorem step_empty_todo (g : Word → Word) (cap : Word) (seen kept : List Word) (fuel : Nat)
    (prev : Option Word) :
    boundaryStep g (boundaryState cap [] seen fuel prev kept) =
      boundaryState cap [] seen fuel prev kept := by
  simp [boundaryStep, boundaryState, unpairB_pairB, encodeFrontier]

private theorem step_empty_fuel (g : Word → Word) (cap : Word) (xs seen kept : List Word)
    (prev : Option Word) :
    boundaryStep g (boundaryState cap xs seen 0 prev kept) =
      boundaryState cap xs seen 0 prev kept := by
  simp [boundaryStep, boundaryState, unpairB_pairB, un, sel]

private theorem boundaryStep_cons (g : Word → Word) (queries : Word → List Word)
    (gs : ∀ x, g x = encodeFrontier (queries x)) (cap : Word) (x : Word)
    (xs seen kept : List Word) (fuel : Nat) (prev : Option Word) (hs : (g x).length ≤ cap.length) :
    boundaryStep g (boundaryState cap (x :: xs) seen (fuel+1) prev kept) =
      if ∃ y ∈ queries x, y ∉ seen then
        boundaryState cap xs (seen ++ queries x) fuel (some x) (kept ++ prev.toList)
      else boundaryState cap xs seen (fuel+1) (some x) kept := by
  have hne : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
  have ec : encodeFrontier (x::xs) = pairB x (encodeFrontier xs) := rfl
  have eprev : encodeFrontier [x] = pairB x [] := rfl
  have hc : (encodeFrontier (queries x)).length ≤ cap.length := by simpa [gs] using hs
  have hf := freshQuery_spec seen (queries x)
  by_cases h : ∃ y ∈ queries x, y ∉ seen
  · simp [boundaryStep, boundaryState, unpairB_pairB, ec, eprev, hne, un, List.replicate_succ,
      bflag, gs, hc, hf.mpr h, h, sel, encodeFrontier_append_words]
  · have hfalse : freshQuery (encodeFrontier seen) (encodeFrontier (queries x)) = false := by
      cases he : freshQuery (encodeFrontier seen) (encodeFrontier (queries x))
      · rfl
      · exact False.elim (h (hf.mp he))
    simp [boundaryStep, boundaryState, unpairB_pairB, ec, eprev, hne, un, List.replicate_succ,
      bflag, gs, hc, hfalse, h, sel]

private theorem boundaryRun (g : Word → Word) (queries : Word → List Word)
    (gs : ∀ x, g x = encodeFrontier (queries x)) (cap : Word) (xs : List Word) :
    ∀ k : Nat, xs.length ≤ k → ∀ (seen kept : List Word) (fuel : Nat) (prev : Option Word),
      (∀ x ∈ xs, (g x).length ≤ cap.length) →
      boundaryRead ((boundaryStep g)^[k] (boundaryState cap xs seen fuel prev kept)) =
        encodeFrontier (kept ++ rightPrune queries xs fuel seen prev) := by
  induction xs with
  | nil =>
    intro k _ seen kept fuel prev _
    rw [Function.iterate_fixed (step_empty_todo g cap seen kept fuel prev) k]
    cases fuel <;> simp [boundaryRead, boundaryState, unpairB_pairB, rightPrune, un,
      List.replicate_succ, encodeFrontier_append_words]
  | cons x xs ih =>
    intro k hk seen kept fuel prev hcap
    cases fuel with
    | zero =>
      rw [Function.iterate_fixed (step_empty_fuel g cap (x :: xs) seen kept prev) k]
      simp [boundaryRead, boundaryState, unpairB_pairB, rightPrune, un]
    | succ fuel =>
      cases k with
      | zero => simp at hk
      | succ k =>
        rw [Function.iterate_succ_apply, boundaryStep_cons g queries gs cap x xs seen kept fuel prev
          (hcap x List.mem_cons_self)]
        have hb : ∀ x ∈ xs, (g x).length ≤ cap.length :=
          fun x hx => hcap x (List.mem_cons_of_mem _ hx)
        have hle : xs.length ≤ k := by simpa using hk
        by_cases h : ∃ y ∈ queries x, y ∉ seen
        · rw [if_pos h, ih k hle (seen ++ queries x) (kept ++ prev.toList) fuel (some x) hb]
          simp [rightPrune, h, List.append_assoc]
        · rw [if_neg h, ih k hle seen kept (fuel+1) (some x) hb]
          simp [rightPrune, h]

private def runBoundary (g : Word → Word) (r : Polynomial Nat) (s : Word) : Word :=
  let xs := (unpairB s).2
  let cap := un (r.eval s.length)
  let init := pairB cap (pairB xs (pairB [] (pairB (true :: (unpairB s).1) (pairB [] []))))
  boundaryRead ((boundaryStep g)^[s.length] init)

private theorem runBoundary_cpt {g : Word → Word} (hg : CPT g) (r : Polynomial Nat) :
    CPT (runBoundary g r) := by
  obtain ⟨c⟩ := boundaryStep_cpt hg
  have h := Iter.iter_polyTime_measure (boundaryStep g) c boundaryMeasure 7
    (boundaryMeasure_step g) (boundaryStep_size g) (fun s => by
      have hh := unpairB_length s
      unfold boundaryMeasure
      omega)
  have hi := cpt_pairB2 (L055 r) (cpt_pairB2 cpt_unpairB2
    (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_cons1 true cpt_unpairB1) (cpt_const (pairB [] [])))))
  exact bf_cptl (cpt_comp (cpt_comp (cpt_pair hi cpt_id) h) boundaryRead_cpt) (fun _ => rfl)

private theorem runBoundary_spec (queries : Word → List Word) (g : Word → Word) (r : Polynomial Nat)
    (gs : ∀ x, g x = encodeFrontier (queries x)) (hr : ∀ x, (g x).length ≤ r.eval (List.length x))
    (b : Nat) (xs : List Word) :
    runBoundary g r (pairB (un b) (encodeFrontier xs)) =
      encodeFrontier (rightPrune queries xs (b+1) [] none) := by
  let s := pairB (un b) (encodeFrontier xs)
  let cap := un (r.eval s.length)
  have hword (x : Word) (hx : x ∈ xs) : x.length ≤ (encodeFrontier xs).length := by
    induction xs with
    | nil => simp at hx
    | cons y ys ih =>
      change x.length ≤ (pairB y (encodeFrontier ys)).length
      rw [pairB_length]
      rcases List.mem_cons.mp hx with rfl | hy
      · omega
      · have h := ih hy
        omega
  have hcap (x : Word) (hx : x ∈ xs) : (g x).length ≤ cap.length := by
    have henc : (encodeFrontier xs).length ≤ s.length := by
      simp only [s, pairB_length]
      omega
    have h' := (hword x hx).trans henc
    simpa [cap, un_length] using (hr x).trans (eval_mono r h')
  have hlen : xs.length ≤ s.length := by
    have := encodeFrontier_length xs
    simp only [s, pairB_length]
    omega
  have he := boundaryRun g queries gs cap xs s.length hlen [] [] (b+1) none hcap
  change runBoundary g r s = _
  unfold runBoundary
  simp only [s, unpairB_pairB]
  change boundaryRead ((boundaryStep g)^[s.length] (boundaryState cap xs [] (b+1) none [])) = _
  simpa using he

theorem MeasuredSparseConjunctiveBoundary (queries : Word → List Word)
    (hf : CPT (fun x => (queries x).foldr
      (fun a b => List.replicate a.length true ++ false :: (a ++ b)) [])) :
    ∃ prune : Word → Word, CPT prune ∧
      ∃ keep : Nat → List Word → List Word,
      (∀ b xs,
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        prune (consWord (List.replicate b true) (xs.foldr consWord [])) =
          (keep b xs).foldr consWord [] ∧
        (keep b xs).Sublist xs ∧ (keep b xs).length ≤ b + 2) ∧
      ∀ (b : Nat) (S : Finset Word), S.card ≤ b →
        ∀ (good rest : List Word) (x : Word),
          (∀ y ∈ good ++ [x], ∀ w ∈ queries y, w ∈ S) →
          (rest = [] ∨ ∃ y ys, rest = y :: ys ∧ ∃ w ∈ queries y, w ∉ S) →
          x ∈ keep b ((good ++ [x]) ++ rest) := by
  let g := fun x => encodeFrontier (queries x)
  obtain ⟨r, hr⟩ := output_length_poly g hf
  refine ⟨runBoundary g r, runBoundary_cpt hf r, fun b xs => rightPrune queries xs (b+1) [] none,
    fun b xs => ⟨runBoundary_spec queries g r (fun _ => rfl) hr b xs,
      (rightPrune_public queries).1 b xs⟩, (rightPrune_public queries).2⟩

end PEqualNP.Outside
