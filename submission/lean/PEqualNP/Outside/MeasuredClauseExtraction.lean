import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def step (split : List Bool → List Bool × List Bool) (s : List Bool) : List Bool :=
  let p := split (unpairB s).1
  pairB p.2 ((unpairB s).2 ++ p.1)

private theorem step_cpt {split : List Bool → List Bool × List Bool}
    (hs : ComputableInPolyTime (fun x : List Bool => x) encodePair split) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step split) := by
  have h := cpt_comp cpt_unpairB1 hs
  exact cpt_pairB2 (cpt_comp h cpt_snd) (cpt_app2 cpt_unpairB2 (cpt_comp h cpt_fst))

private theorem step_length {split : List Bool → List Bool × List Bool}
    (h : ∀ x, (split x).1 ++ (split x).2 = x) (s : List Bool) :
    (step split s).length ≤ s.length+1 := by
  have h1 := unpairB_length s
  have h2 := congrArg List.length (h (unpairB s).1)
  simp only [List.length_append] at h2
  simp only [step,pairB_length,List.length_append]
  omega

private theorem encode_app (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF,List.flatMap_append]

private theorem encode_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]

private theorem run {split : List Bool → List Bool × List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hz : split [] = ([],[])) (φ : CNF) (acc : List Bool) (i : ℕ) :
    (step split)^[i] (pairB (encodeCNF φ) acc) =
      pairB (encodeCNF (φ.drop i)) (acc ++ encodeCNF (φ.take i)) := by
  induction i generalizing φ acc with
  | zero => simp [encodeCNF]
  | succ i ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have e : step split (pairB (encodeCNF []) acc) = pairB (encodeCNF []) acc := by
            simp [step,encodeCNF,unpairB_pairB,hz]
          rw [e,ih]
          simp
      | cons c φ =>
          have e : step split (pairB (encodeCNF (c :: φ)) acc) =
              pairB (encodeCNF φ) (acc ++ encodeClause c) := by
            simp only [step,unpairB_pairB,encode_cons,hs]
          rw [e,ih,List.drop_succ_cons,List.take_succ_cons,encode_cons,List.append_assoc]

private theorem extract_tail {split : List Bool → List Bool × List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hz : split [] = ([],[])) (φ : CNF) (i : ℕ) :
    split (encodeCNF (φ.drop i)) =
      (encodeCNF (getElem? φ i).toList,encodeCNF (φ.drop (i+1))) := by
  by_cases hi : i < φ.length
  · rw [List.drop_eq_getElem_cons hi,List.getElem?_eq_getElem hi,encode_cons,hs]
    simp only [Option.toList_some,encode_cons]
    simp [encodeCNF]
  · have hle : φ.length ≤ i := by omega
    rw [List.drop_eq_nil_iff.mpr hle,List.drop_eq_nil_iff.mpr (by omega),
      show getElem? φ i = none from List.getElem?_eq_none hle]
    exact hz

/-- Remove one canonical clause at a unary index, returning its encoding separately.
An out-of-range index returns the unchanged formula and an empty second component. -/
theorem MeasuredClauseExtraction :
    ∃ pull : List Bool × List Bool → List Bool × List Bool,
      ComputableInPolyTime encodePair encodePair pull ∧
      ∀ (φ : CNF) (index : List Bool),
        pull (index,encodeCNF φ) =
          (encodeCNF (φ.eraseIdx index.length),encodeCNF (Option.toList (getElem? φ index.length))) := by
  obtain ⟨split,hs,hjoin,hspec⟩ := measuredFirstClause_reassembles
  have hz : split [] = ([],[]) := by
    obtain ⟨ha,hb⟩ := List.append_eq_nil_iff.mp (hjoin [])
    exact Prod.ext ha hb
  let start := fun s => pairB (unpairB s).2 []
  let loop := fun s => (step split)^[(unpairB s).1.length] (start s)
  let result := fun s =>
    let p := unpairB (loop s)
    let parts := split p.1
    (p.2 ++ parts.2,parts.1)
  have hloop : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) loop :=
    cpt_iterGrow (step_cpt hs) 1 (step_length hjoin) cpt_unpairB1
      (cpt_pairB2 cpt_unpairB2 (cpt_const []))
  have hpart := cpt_comp (cpt_unpairB1_1 hloop) hs
  have hr : ComputableInPolyTime (fun x : List Bool => x) encodePair result :=
    cpt_pair (cpt_app2 (cpt_unpairB2_1 hloop) (cpt_comp hpart cpt_snd)) (cpt_comp hpart cpt_fst)
  refine ⟨fun p => result (pairB p.1 p.2),cpt_comp (g := result) cpt_pairB hr,fun φ index => ?_⟩
  simp only [result,loop,start,unpairB_pairB]
  rw [run hspec hz,unpairB_pairB,extract_tail hspec hz,List.nil_append,
    ← encode_app,List.eraseIdx_eq_take_drop_succ]

end PEqualNP.Outside
