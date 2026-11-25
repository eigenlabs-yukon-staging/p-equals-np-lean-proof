import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def step (split : List Bool → List Bool × List Bool) (test : List Bool → Bool) (s : List Bool) :
    List Bool :=
  let remaining := (unpairB s).1
  let c := (split remaining).1
  let tail := (split remaining).2
  let yes := (unpairB (unpairB s).2).1
  let no := (unpairB (unpairB s).2).2
  if remaining = [] then s
  else if test c then pairB tail (pairB (c ++ yes) no)
  else pairB tail (pairB yes (c ++ no))

private theorem step_cpt {split : List Bool → List Bool × List Bool} {test : List Bool → Bool}
    (hs : ComputableInPolyTime (fun x : List Bool => x) encodePair split)
    (ht : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step split test) := by
  have hr := cpt_unpairB1
  have hsp := cpt_comp hr hs
  have hc := cpt_comp hsp cpt_fst
  have htail := cpt_comp hsp cpt_snd
  have hy := cpt_unpairB1_1 cpt_unpairB2
  have hn := cpt_unpairB2_1 cpt_unpairB2
  have flag := cpt_bitFlag (cpt_comp hc ht)
  have yBranch := cpt_pairB2 (cpt_app2 hc hy) hn
  have nBranch := cpt_pairB2 hy (cpt_app2 hc hn)
  refine cptE (cpt_sel hr cpt_id (cpt_pairB2 htail (cpt_sel flag nBranch yBranch))) (fun s => ?_)
  simp only [step,sel]
  split
  · rfl
  · cases test (split (unpairB s).1).1 <;> rfl

private theorem step_length {split : List Bool → List Bool × List Bool}
    (h : ∀ x, (split x).1 ++ (split x).2 = x) (test : List Bool → Bool) (s : List Bool) :
    (step split test s).length ≤ s.length+2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := congrArg List.length (h (unpairB s).1)
  simp only [List.length_append] at h3
  dsimp only [step]
  split
  · omega
  · split <;> simp only [pairB_length,List.length_append] <;> omega

private theorem run {split : List Bool → List Bool × List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (test : List Bool → Bool) (φ : CNF) (a b : List Bool) (n : ℕ) (hn : φ.length ≤ n) :
    (step split test)^[n] (pairB (encodeCNF φ) (pairB a b)) =
      pairB [] (pairB (encodeCNF ((φ.filter (fun c => test (encodeClause c))).reverse) ++ a)
        (encodeCNF ((φ.filter (fun c => !test (encodeClause c))).reverse) ++ b)) := by
  induction n generalizing φ a b with
  | zero =>
      have h : φ = [] := List.length_eq_zero_iff.mp (by omega)
      subst φ
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have he : step split test (pairB (encodeCNF []) (pairB a b)) =
            pairB (encodeCNF []) (pairB a b) := by simp [step,encodeCNF,unpairB_pairB]
          rw [he,ih [] _ _ (by simp)]
      | cons c φ =>
          have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
          have hne : encodeClause c ++ encodeCNF φ ≠ [] := by simp [encodeClause]
          have htail : φ.length ≤ n := by simpa using hn
          rw [he]
          simp only [step,unpairB_pairB,hs,ite_eq_right hne]
          cases hc : test (encodeClause c)
          · simp only [hc,Bool.false_eq_true,ite_false,ih _ _ _ htail]
            simp [hc,encodeCNF,List.flatMap_append,List.append_assoc]
          · simp only [hc,ite_true,ih _ _ _ htail]
            simp [hc,encodeCNF,List.flatMap_append,List.append_assoc]

private theorem cnf_length (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      change φ.length+1 ≤ (encodeClause c ++ encodeCNF φ).length
      simp only [encodeClause,List.length_append,List.length_cons,List.length_nil]
      omega

/-- A measured Boolean predicate on encoded clauses induces a measured partition
of canonical reference formulae into the chosen and rejected clause lists. -/
theorem MeasuredCNFPartition (test : List Bool → Bool)
    (ht : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test) :
    ∃ pack : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pack ∧
      ∀ φ : CNF,
        let a := encodeCNF ((φ.filter (fun c => test (encodeClause c))).reverse)
        let b := encodeCNF ((φ.filter (fun c => !test (encodeClause c))).reverse)
        pack (encodeCNF φ) = List.replicate a.length true ++ false :: (a ++ b) := by
  obtain ⟨split,hs,hjoin,hspec⟩ := measuredFirstClause_reassembles
  let initial := fun x => pairB x (pairB [] [])
  let pack := fun x => (unpairB ((step split test)^[x.length] (initial x))).2
  have hi := cpt_pairB2 cpt_id (cpt_const (pairB [] []))
  have hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pack :=
    cpt_unpairB2_1 (cpt_iterGrow (step_cpt hs ht) 2 (step_length hjoin test) cpt_id hi)
  refine ⟨pack,hp,fun φ => ?_⟩
  simp only [pack,initial,run hspec test φ [] [] _ (cnf_length φ),List.append_nil,unpairB_pairB]
  rfl

end PEqualNP.Outside
