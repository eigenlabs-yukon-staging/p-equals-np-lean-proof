import PEqualNP.Outside.SparseRepresentativesMachine
import PEqualNP.Library.Machines.IterMeasure

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Word" => List Bool

theorem encodeFrontier_append_words (xs ys : List Word) :
    encodeFrontier (xs ++ ys) = encodeFrontier xs ++ encodeFrontier ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change pairB x (encodeFrontier (xs ++ ys)) =
      pairB x (encodeFrontier xs) ++ encodeFrontier ys
    simp [ih, pairB, List.append_assoc]

private def expansionStep (g : Word → Word) (s : Word) : Word :=
  let cap := (unpairB s).1
  let todo := (unpairB (unpairB s).2).1
  let kept := (unpairB (unpairB s).2).2
  let expanded := g (unpairB todo).1
  let next := (unpairB todo).2
  let kept' := sel (bflag (decide (expanded.length ≤ cap.length))) kept (kept ++ expanded)
  sel todo s (pairB cap (pairB next kept'))

private def expansionMeasure (s : Word) : Nat := (unpairB s).1.length + 2

private theorem expand_measure_step (g : Word → Word) (s : Word) :
    expansionMeasure (expansionStep g s) ≤ expansionMeasure s := by
  unfold expansionStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [expansionMeasure, unpairB_pairB]

private theorem expansionStep_size (g : Word → Word) (s : Word) :
    (expansionStep g s).length ≤ s.length + expansionMeasure s := by
  have hs := unpairB_length s
  have hr := unpairB_length (unpairB s).2
  have ht := unpairB_length (unpairB (unpairB s).2).1
  unfold expansionStep expansionMeasure
  dsimp only
  unfold sel
  split
  · omega
  · simp only [pairB_length]
    split
    · omega
    · rename_i hc
      have hb := not_congr (bflag_eq_nil (decide
        ((g (unpairB (unpairB (unpairB s).2).1).1).length ≤ (unpairB s).1.length)))
      have hh := hb.mp hc
      simp only [Bool.not_eq_false, decide_eq_true_eq] at hh
      rw [List.length_append]
      omega

private theorem expansionStep_polyTime {g : Word → Word} (hg : CPT g) :
    CPT (expansionStep g) := by
  have hc := cpt_unpairB1
  have ht := cpt_unpairB1_1 cpt_unpairB2
  have hk := cpt_unpairB2_1 cpt_unpairB2
  have he := cpt_comp (cpt_unpairB1_1 ht) hg
  have flag := cpt_bitFlag (cpt_comp (cpt_pair hc he) LenCmp.lenLE_polyTime)
  exact bf_cptl (cpt_sel ht cpt_id (cpt_pairB2 hc (cpt_pairB2 (cpt_unpairB2_1 ht)
    (cpt_sel flag hk (cpt_app2 hk he))))) (fun _ => rfl)

private theorem expansionIter_polyTime {g : Word → Word} (hg : CPT g)
    {clock init : Word → Word} (hclock : CPT clock) (hinit : CPT init) :
    CPT (fun s => (expansionStep g)^[(clock s).length] (init s)) := by
  obtain ⟨c⟩ := expansionStep_polyTime hg
  have hi := Iter.iter_polyTime_measure (expansionStep g) c expansionMeasure 2
    (expand_measure_step g) (expansionStep_size g) (fun s => by
      have h := unpairB_length s
      unfold expansionMeasure
      omega)
  exact bf_cptl (cpt_comp (cpt_pair hinit hclock) hi) (fun _ => rfl)

private def expansionState (cap : Word) (xs ys : List Word) : Word :=
  pairB cap (pairB (encodeFrontier xs) (encodeFrontier ys))

private theorem expansionIter_spec (children : Word → List Word)
    (g : Word → Word) (gspec : ∀ x, g x = encodeFrontier (children x))
    (cap : Word) (xs : List Word) :
    ∀ n : Nat, xs.length ≤ n → ∀ (ys : List Word),
      (∀ x ∈ xs, (g x).length ≤ cap.length) →
      (expansionStep g)^[n] (expansionState cap xs ys) =
        expansionState cap [] (ys ++ xs.flatMap children) := by
  induction xs with
  | nil =>
    intro n _ ys _
    have h : expansionStep g (expansionState cap [] ys) = expansionState cap [] ys := by
      simp [expansionStep, expansionState, encodeFrontier, unpairB_pairB]
    simpa using Function.iterate_fixed h n
  | cons x xs ih =>
    intro n hn ys hcap
    cases n with
    | zero => simp at hn
    | succ n =>
      have hstep : expansionStep g (expansionState cap (x :: xs) ys) =
          expansionState cap xs (ys ++ children x) := by
        have hx : (g x).length ≤ cap.length := hcap x List.mem_cons_self
        rw [gspec] at hx
        have es : encodeFrontier (x :: xs) = pairB x (encodeFrontier xs) := rfl
        have en : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
        simp [expansionStep, expansionState, es, en, unpairB_pairB, sel, bflag, hx,
          encodeFrontier_append_words, gspec]
      rw [Function.iterate_succ_apply, hstep, ih n (by simpa using hn)]
      · simp [List.flatMap_cons, List.append_assoc]
      · exact fun x hx => hcap x (List.mem_cons_of_mem _ hx)

def expandFrontier (g : Word → Word) (r : Polynomial Nat) (s : Word) : Word :=
  let cap := List.replicate (r.eval s.length) true
  let out := (expansionStep g)^[s.length] (pairB cap (pairB s []))
  (unpairB (unpairB out).2).2

theorem expandFrontier_polyTime {g : Word → Word} (hg : CPT g) (r : Polynomial Nat) :
    CPT (expandFrontier g r) := by
  have h := expansionIter_polyTime hg cpt_id (cpt_pairB2 (L055 r)
    (cpt_pairB2 cpt_id (cpt_const [])))
  exact bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 h)) (fun _ => rfl)

theorem expandFrontier_spec (children : Word → List Word)
    (g : Word → Word) (gspec : ∀ x, g x = encodeFrontier (children x))
    (r : Polynomial Nat) (size : ∀ x : Word, (g x).length ≤ r.eval x.length)
    (xs : List Word) :
    expandFrontier g r (encodeFrontier xs) = encodeFrontier (xs.flatMap children) := by
  have hlen (x : Word) (hx : x ∈ xs) : x.length ≤ (encodeFrontier xs).length := by
    induction xs with
    | nil => simp at hx
    | cons a as ih =>
      change x.length ≤ (pairB a (encodeFrontier as)).length
      rw [pairB_length]
      rcases List.mem_cons.mp hx with he | hm
      · subst x; omega
      · have := ih hm; omega
  let cap := List.replicate (r.eval (encodeFrontier xs).length) true
  have hc (x : Word) (hx : x ∈ xs) : (g x).length ≤ cap.length :=
    by simpa [cap] using (size x).trans (eval_mono r (hlen x hx))
  have ht := expansionIter_spec children g gspec cap xs _ (encodeFrontier_length xs) [] hc
  have he : pairB cap (pairB (encodeFrontier xs) []) = expansionState cap xs [] := rfl
  unfold expandFrontier
  dsimp only
  change (unpairB (unpairB ((expansionStep g)^[(encodeFrontier xs).length]
    (pairB cap (pairB (encodeFrontier xs) [])))).2).2 = _
  rw [he, ht]
  simp [expansionState, unpairB_pairB]

/-- A polynomial-time word machine that emits an encoded list for each input word
lifts to a polynomial-time flat map on encoded lists. -/
theorem FrontierExpansionMachine (g : Word → Word) (hg : CPT g)
    (children : Word → List Word)
    (gspec : ∀ x, g x =
      (children x).foldr (fun a b => List.replicate a.length true ++ false :: (a ++ b)) []) :
    ∃ run : Word → Word, CPT run ∧
      ∀ xs : List Word,
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (xs.foldr consWord []) = (xs.flatMap children).foldr consWord [] := by
  obtain ⟨r, hr⟩ := output_length_poly g hg
  exact ⟨expandFrontier g r, expandFrontier_polyTime hg r,
    expandFrontier_spec children g gspec r hr⟩

end PEqualNP.Outside
