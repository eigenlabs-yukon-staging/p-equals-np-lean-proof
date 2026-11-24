import PEqualNP.Outside.TruthTableSparseNextWitness
import Mathlib.Data.Finset.Sort

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open TruthTableSolver

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

private def enumState (cap x cursor out : Word) : Word := pairB (pairB cap x) (pairB cursor out)

private def enumStep (next : Word × Word → Word) (s : Word) : Word :=
  let header := (unpairB s).1
  let body := (unpairB s).2
  let value := next ((unpairB header).2,(unpairB body).1)
  let update := pairB header (pairB value ((unpairB body).2 ++ pairB value.tail []))
  sel value s (sel (bflag (decide (value.length ≤ (unpairB header).1.length))) s update)

private theorem enumStep_cpt {next : Word × Word → Word}
    (hc : ComputableInPolyTime encodePair (fun x => x) next) : CPT (enumStep next) := by
  have hx := cpt_unpairB2_1 cpt_unpairB1
  have hcursor := cpt_unpairB1_1 cpt_unpairB2
  have hcap := cpt_unpairB1_1 cpt_unpairB1
  have hval := cpt_comp (cpt_pair hx hcursor) hc
  have hguard := cpt_bitFlag (cpt_comp (cpt_pair hcap hval) LenCmp.lenLE_polyTime)
  have hout := cpt_app2 (cpt_unpairB2_1 cpt_unpairB2)
    (cpt_pairB2 (cpt_tail1 hval) (cpt_const []))
  have hupdate := cpt_pairB2 cpt_unpairB1 (cpt_pairB2 hval hout)
  exact bf_cptl (cpt_sel hval cpt_id (cpt_sel hguard cpt_id hupdate)) (fun _ => rfl)

private def enumMeasure (s : Word) : Nat := 4 * (unpairB (unpairB s).1).1.length + 3

private theorem enumMeasure_le (s : Word) : enumMeasure s ≤ 4*s.length + 4 := by
  have h := unpairB_length s
  have hh := unpairB_length (unpairB s).1
  unfold enumMeasure
  omega

private theorem enumMeasure_step (next : Word × Word → Word) (s : Word) :
    enumMeasure (enumStep next s) ≤ enumMeasure s := by
  unfold enumStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · simp [enumMeasure,unpairB_pairB]

private theorem enumStep_size (next : Word × Word → Word) (s : Word) :
    (enumStep next s).length ≤ s.length + enumMeasure s := by
  have hs := unpairB_length s
  have hb := unpairB_length (unpairB s).2
  unfold enumStep
  dsimp only
  unfold sel
  split
  · omega
  · split
    · omega
    · rename_i h
      have hl := (not_congr (bflag_eq_nil _)).mp h
      simp only [Bool.not_eq_false, decide_eq_true_eq] at hl
      simp only [pairB_length,List.length_append,List.length_tail, List.length_nil,
        enumMeasure]
      omega

private theorem enumRun_cpt {next : Word × Word → Word}
    (hnext : ComputableInPolyTime encodePair (fun x => x) next) (p : Polynomial Nat) :
    ComputableInPolyTime encodePair (fun x => x) (fun q : Word × Word =>
      let cap := un ((p+1).eval q.1.length)
      (unpairB (unpairB ((enumStep next)^[q.2.length] (enumState cap q.1 [] []))).2).2) := by
  obtain ⟨machine⟩ := enumStep_cpt hnext
  have h := Iter.iter_polyTime_measure (enumStep next) machine enumMeasure 4
    (enumMeasure_step next) (enumStep_size next) enumMeasure_le
  have hcap := cpt_comp cpt_unpairB1 (L055 (p+1))
  have init := cpt_pairB2 (cpt_pairB2 hcap cpt_unpairB1) (cpt_const (pairB [] []))
  have hraw := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_comp (cpt_pair init cpt_unpairB2) h))
  refine bf_cptl (cpt_comp cpt_pairB hraw) ?_
  rintro ⟨x,fuel⟩
  simp [enumState,unpairB_pairB,un]

private def eligible (cursor w : Word) : Prop := cursor = [] ∨ cursor.tail < w

private def NextSpec (R : Set (Word × Word)) (next : Word × Word → Word) : Prop :=
  ∀ x c : Word,
    (next (x,c) = [] ∧ ∀ w : Word, (x,w) ∈ R → ¬ eligible c w) ∨
    ∃ w : Word, next (x,c) = true::w ∧ (x,w) ∈ R ∧ eligible c w ∧
      ∀ u : Word, (x,u) ∈ R → eligible c u → w ≤ u

private theorem next_nil {R : Set (Word × Word)} {next : Word × Word → Word}
    (spec : NextSpec R next) (x c : Word)
    (none : ∀ w : Word, ¬ ((x,w) ∈ R ∧ eligible c w)) : next (x,c) = [] := by
  rcases spec x c with hn | ⟨w,_,hw,hc,_⟩
  · exact hn.1
  · exact False.elim (none w ⟨hw,hc⟩)

private theorem next_head {R : Set (Word × Word)} {next : Word × Word → Word}
    (spec : NextSpec R next) (x c w : Word) (ws : List Word)
    (sorted : (w::ws).Pairwise (· < ·))
    (cover : ∀ u : Word, u ∈ w::ws ↔ (x,u) ∈ R ∧ eligible c u) :
    next (x,c) = true::w := by
  have hw := (cover w).mp (by simp)
  rcases spec x c with ⟨_,hn⟩ | ⟨v,hv,hr,he,hm⟩
  · exact False.elim (hn w hw.1 hw.2)
  · have hmem := (cover v).mpr ⟨hr,he⟩
    rcases List.mem_cons.mp hmem with eq | tail
    · simpa [eq] using hv
    · have hlt := (List.pairwise_cons.mp sorted).1 v tail
      exact False.elim ((not_lt_of_ge (hm w hw.1 hw.2)) hlt)

private theorem eligible_trans {c u w : Word} (h : eligible c u) (h' : u < w) :
    eligible c w := by
  rcases h with eq | lt
  · exact Or.inl eq
  · exact Or.inr (lt.trans h')

private theorem enumIter {R : Set (Word × Word)} {next : Word × Word → Word}
    (spec : NextSpec R next) (x cap c : Word) (out ws : List Word) (n : Nat)
    (sorted : ws.Pairwise (· < ·))
    (cover : ∀ w : Word, w ∈ ws ↔ (x,w) ∈ R ∧ eligible c w)
    (bound : ∀ w : Word, (x,w) ∈ R → w.length + 1 ≤ cap.length) :
    ∃ cursor : Word,
      (enumStep next)^[n] (enumState cap x c (encodeFrontier out)) =
        enumState cap x cursor (encodeFrontier (out ++ ws.take n)) := by
  induction n generalizing c out ws with
  | zero => exact ⟨c,by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      have hnil : next (x,c) = [] := next_nil spec x c (fun w hw => by simpa using (cover w).mpr hw)
      have hstep : enumStep next (enumState cap x c (encodeFrontier out)) =
          enumState cap x c (encodeFrontier out) := by
        simp [enumStep,enumState,unpairB_pairB,hnil]
      rw [hstep]
      obtain ⟨cursor,h⟩ := ih c out [] sorted cover
      exact ⟨cursor,by simpa using h⟩
    | cons w ws =>
      have hnext := next_head spec x c w ws sorted cover
      have hw := (cover w).mp (by simp)
      have hb := bound w hw.1
      have hstep : enumStep next (enumState cap x c (encodeFrontier out)) =
          enumState cap x (true::w) (encodeFrontier (out ++ [w])) := by
        have henc : encodeFrontier [w] = pairB w [] := rfl
        simp [enumStep,enumState,unpairB_pairB,sel,bflag,hnext,hb,encodeFrontier_append_words,henc]
      have hcover (u : Word) : u ∈ ws ↔ (x,u) ∈ R ∧ eligible (true::w) u := by
        constructor
        · intro hu
          have huR := ((cover u).mp (List.mem_cons_of_mem _ hu)).1
          have huLt := (List.pairwise_cons.mp sorted).1 u hu
          exact ⟨huR,Or.inr huLt⟩
        · rintro ⟨huR,he⟩
          have hlu : w < u := by simpa [eligible] using he
          have hmem := (cover u).mpr ⟨huR,eligible_trans hw.2 hlu⟩
          exact (List.mem_cons.mp hmem).resolve_left (fun eq => (ne_of_lt hlu) eq.symm)
      rw [hstep]
      obtain ⟨cursor,h⟩ := ih (true::w) (out ++ [w]) ws sorted.of_cons hcover
      exact ⟨cursor,by simpa [List.append_assoc] using h⟩

private theorem sortedWitnesses (R : Set (Word × Word)) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length) (x : Word) :
    ∃ ws : List Word, ws.Pairwise (· < ·) ∧ ∀ w : Word, w ∈ ws ↔ (x,w) ∈ R := by
  classical
  let A : Language Bool := {w | (x,w) ∈ R}
  let S := acceptedShort A (p.eval x.length)
  refine ⟨S.sort (· ≤ ·),List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S),fun w => ?_⟩
  rw [Finset.mem_sort]
  exact ⟨fun h => (acceptedShort_spec A _ _ h).1,
    fun h => mem_acceptedShort A _ _ h (bound x w h)⟩

private theorem measuredEnumeration (R : Set (Word × Word)) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length)
    (next : Word × Word → Word) (hnext : ComputableInPolyTime encodePair (fun x => x) next)
    (spec : NextSpec R next) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (x fuel : Word) (ws : List Word), ws.Pairwise (· < ·) →
        (∀ w : Word, w ∈ ws ↔ (x,w) ∈ R) →
        run (x,fuel) = encodeFrontier (ws.take fuel.length) := by
  let run := fun q : Word × Word =>
    let cap := un ((p+1).eval q.1.length)
    (unpairB (unpairB ((enumStep next)^[q.2.length] (enumState cap q.1 [] []))).2).2
  refine ⟨run,enumRun_cpt hnext p,fun x fuel ws hsort hcomplete => ?_⟩
  let cap := un ((p+1).eval x.length)
  have hc (w : Word) : w ∈ ws ↔ (x,w) ∈ R ∧ eligible [] w := by simp [hcomplete,eligible]
  have hb (w : Word) (hw : (x,w) ∈ R) : w.length + 1 ≤ cap.length := by
    simpa [cap] using Nat.succ_le_succ (bound x w hw)
  obtain ⟨c,h⟩ := enumIter spec x cap [] [] ws fuel.length hsort hc hb
  have hh : (enumStep next)^[fuel.length] (enumState cap x [] []) =
      enumState cap x c (encodeFrontier (ws.take fuel.length)) := by
    simpa [encodeFrontier] using h
  change (unpairB (unpairB ((enumStep next)^[fuel.length] (enumState cap x [] []))).2).2 = _
  rw [hh]
  simp [enumState,unpairB_pairB]

/-- Produce the first unary-budgeted number of distinct accepted witnesses,
in increasing lexicographic order, in the pinned polynomial-time model. -/
theorem TruthTableSparseWitnessEnumeration (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔
      T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      (∀ x : Word, ∃ ws : List Word, ws.Pairwise (· < ·) ∧ ∀ w : Word, w ∈ ws ↔ (x,w) ∈ R) ∧
      ∀ (x fuel : Word) (ws : List Word), ws.Pairwise (· < ·) →
        (∀ w : Word, w ∈ ws ↔ (x,w) ∈ R) →
        run (x,fuel) = (ws.take fuel.length).foldr
          (fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)) [] := by
  obtain ⟨next,hn,hs⟩ := TruthTableSparseNextWitness R hR p bound A B hA s sparse k q hq T hT relation
  obtain ⟨run,hr,hspec⟩ := measuredEnumeration R p bound next hn hs
  exact ⟨run,hr,sortedWitnesses R p bound,hspec⟩

end PEqualNP.Outside
