import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def short (r : List Bool) : Bool :=
  isEnd r || isEnd (dropI r) || isEnd (dropI (dropI r))

private def step (split : List Bool → List Bool × List Bool) (s : List Bool) : List Bool :=
  let remaining := (unpairB s).1
  let clause := (split remaining).1
  let tail := (split remaining).2
  let small := (unpairB (unpairB s).2).1
  let wide := (unpairB (unpairB s).2).2
  if remaining = [] then s
  else if short clause then pairB tail (pairB (clause ++ small) wide)
  else pairB tail (pairB small (clause ++ wide))

private theorem cpt_short {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bflag (short (f s))) := by
  have hr := cpt_comp hf cpt_dropI
  have hr' := cpt_comp hr cpt_dropI
  have hA := cpt_comp hf cpt_isEndF
  have hB := cpt_comp hr cpt_isEndF
  have hC := cpt_comp hr' cpt_isEndF
  refine cptE (cpt_sel hA (cpt_sel hB hC (cpt_const [true])) (cpt_const [true])) (fun s => ?_)
  unfold short
  cases isEnd (f s) <;> cases isEnd (dropI (f s)) <;> cases isEnd (dropI (dropI (f s))) <;> rfl

private theorem cpt_step {split : List Bool → List Bool × List Bool}
    (hs : ComputableInPolyTime (fun x : List Bool => x) encodePair split) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step split) := by
  have hr := cpt_unpairB1
  have hsp := cpt_comp hr hs
  have hc := cpt_comp hsp cpt_fst
  have ht := cpt_comp hsp cpt_snd
  have ha := cpt_unpairB1_1 cpt_unpairB2
  have hb := cpt_unpairB2_1 cpt_unpairB2
  have hsmall := cpt_pairB2 ht (cpt_pairB2 (cpt_app2 hc ha) hb)
  have hwide := cpt_pairB2 ht (cpt_pairB2 ha (cpt_app2 hc hb))
  refine cptE (cpt_sel hr cpt_id (cpt_sel (cpt_short hc) hwide hsmall)) (fun s => ?_)
  simp only [step, sel]
  split
  · rfl
  · cases short (split (unpairB s).1).1 <;> rfl

private theorem step_length {split : List Bool → List Bool × List Bool}
    (hjoin : ∀ s, (split s).1 ++ (split s).2 = s) (s : List Bool) :
    (step split s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := congrArg List.length (hjoin (unpairB s).1)
  simp only [List.length_append] at h3
  dsimp only [step]
  split
  · omega
  · split <;> simp only [pairB_length, List.length_append] <;> omega

private theorem short_correct (c : Clause) : short (encodeClause c) = decide (c.length ≤ 2) := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  · rfl
  · simp only [short, encodeClause, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      isEnd_lit, dropI_lit, List.length_cons, List.length_nil]
    rfl
  · simp only [short, encodeClause, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, isEnd_lit, dropI_lit, List.length_cons, List.length_nil]
    rfl
  · simp only [short, encodeClause, List.flatMap_cons, List.append_assoc, isEnd_lit,
      dropI_lit, List.length_cons, Bool.false_or]
    exact (decide_eq_false (by omega)).symm

private theorem run_step {split : List Bool → List Bool × List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c, r))
    (φ : CNF) (base wide : List Bool) (n : ℕ) (hn : φ.length ≤ n) :
    (step split)^[n] (pairB (encodeCNF φ) (pairB base wide)) =
      pairB [] (pairB (encodeCNF ((φ.filter (fun c => c.length ≤ 2)).reverse) ++ base)
        (encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse) ++ wide)) := by
  induction n generalizing φ base wide with
  | zero =>
      have hz : φ = [] := List.length_eq_zero_iff.mp (by omega)
      subst φ
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have e : step split (pairB (encodeCNF []) (pairB base wide)) =
              pairB (encodeCNF []) (pairB base wide) := by
            simp [step, unpairB_pairB, encodeCNF]
          rw [e, ih [] _ _ (by simp)]
      | cons c φ =>
          have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
          have hne : encodeClause c ++ encodeCNF φ ≠ [] := by simp [encodeClause]
          have htail : φ.length ≤ n := by simpa using hn
          rw [e]
          simp only [step, unpairB_pairB, hs, ite_eq_right hne, short_correct]
          by_cases hc : c.length ≤ 2
          · have hw : ¬ 2 < c.length := by omega
            simp only [hc, decide_true, ite_true, ih _ _ _ htail]
            simp [hc, hw, encodeCNF, List.flatMap_append, List.append_assoc]
          · have hw : 2 < c.length := by omega
            simp only [hc, decide_false, Bool.false_eq_true, ite_false, ih _ _ _ htail]
            simp [hc, hw, encodeCNF, List.flatMap_append, List.append_assoc]

private theorem formula_length (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      change φ.length + 1 ≤ (encodeClause c ++ encodeCNF φ).length
      simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
      omega

/-- Separate arbitrary reference CNF into its small and wide clauses in measured polynomial time. -/
theorem CNFWideClausePacking :
    ∃ pack : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pack ∧
      ∀ φ : CNF,
        let small := encodeCNF ((φ.filter (fun c => c.length ≤ 2)).reverse)
        let wide := encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse)
        pack (encodeCNF φ) = List.replicate small.length true ++ false :: (small ++ wide) := by
  obtain ⟨split, hsplit, hjoin, hsem⟩ := measuredFirstClause_reassembles
  let init := fun x => pairB x (pairB [] [])
  let pack := fun x => (unpairB ((step split)^[x.length] (init x))).2
  have hinit := cpt_pairB2 cpt_id (cpt_const (pairB [] []))
  have hpack : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pack :=
    cpt_unpairB2_1 (cpt_iterGrow (cpt_step hsplit) 2 (step_length hjoin) cpt_id hinit)
  refine ⟨pack, hpack, fun φ => ?_⟩
  simp only [pack, init, run_step hsem φ [] [] _ (formula_length φ), unpairB_pairB, List.append_nil]
  rfl

end PEqualNP.Outside
