import PEqualNP.Outside.MeasuredRUP
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Outside.RUPSoundness
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private abbrev Raw := List Bool

private def tail (parse : Raw → Raw × Raw) (x : Raw) : Raw := (parse x).2

private def failure (parse : Raw → Raw × Raw) (rup : Raw × Raw → Bool)
    (root rem : Raw) : Raw :=
  if rem = [] then [] else if rup (root ++ (parse rem).2,(parse rem).1) then [] else [true]

private theorem failure_cpt {parse : Raw → Raw × Raw} {rup : Raw × Raw → Bool}
    (hp : ComputableInPolyTime (fun x : Raw => x) encodePair parse)
    (hv : ComputableInPolyTime encodePair Computability.encodeBool rup)
    {root rem : Raw → Raw}
    (hr : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) root)
    (hm : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) rem) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun x => failure parse rup (root x) (rem x)) := by
  have hs := cpt_comp hm hp
  have ht := cpt_comp hs cpt_snd
  have hc := cpt_comp hs cpt_fst
  have hq := cpt_comp (cpt_pair (cpt_app2 hr ht) hc) hv
  refine cptE (cpt_sel hm (cpt_const []) (cpt_sel (cpt_bitFlag hq) (cpt_const [true]) (cpt_const []))) (fun x => ?_)
  unfold failure
  by_cases h : rem x = []
  · simp [sel,h]
  · cases hrup : rup (root x ++ (parse (rem x)).2,(parse (rem x)).1) <;> simp [sel,h,hrup]

private theorem formula_cons (c : Clause) (φ : CNF) : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by
  simp [encodeCNF]

private theorem formula_count (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [formula_cons,List.length_append,List.length_cons]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

private theorem failures_correct (parse : Raw → Raw × Raw) (rup : Raw × Raw → Bool)
    (hp : ∀ (c : Clause) r, parse (encodeClause c ++ r) = (encodeClause c,r))
    (h0 : tail parse [] = [])
    (hv : ∀ (φ : CNF) (c : Clause), rup (encodeCNF φ,encodeClause c) = true ↔ IsRUP (clauseSet φ) c.toFinset)
    (φ ρ : CNF) (n : ℕ) (hn : ρ.length ≤ n) :
    ((List.range n).flatMap (fun i => failure parse rup (encodeCNF φ) ((tail parse)^[i] (encodeCNF ρ)))) = [] ↔
    IsRUPRun (clauseSet φ) (ρ.map (fun c => c.toFinset)) := by
  induction ρ generalizing n with
  | nil =>
      have h (i : ℕ) : (tail parse)^[i] ([] : Raw) = [] := by
        induction i with
        | zero => rfl
        | succ i ih => rw [Function.iterate_succ_apply,h0,ih]
      change ((List.range n).flatMap (fun i => failure parse rup (encodeCNF φ) ((tail parse)^[i] []))) = [] ↔
        IsRUPRun (clauseSet φ) []
      simp only [h,failure,ite_true,List.flatMap_eq_nil_iff,implies_true,true_iff]
      exact .nil
  | cons c ρ ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hlen : ρ.length ≤ n := by simpa using hn
          have hnext (i : ℕ) :
              (tail parse)^[i+1] (encodeCNF (c :: ρ)) = (tail parse)^[i] (encodeCNF ρ) := by
            rw [Function.iterate_succ_apply,formula_cons,tail,hp]
          have htag : encodeCNF (c :: ρ) ≠ [] := by rw [formula_cons]; simp [encodeClause]
          have hc : failure parse rup (encodeCNF φ) (encodeCNF (c :: ρ)) = [] ↔ IsRUP (clauseSet (φ ++ ρ)) c.toFinset := by
            dsimp only [failure]
            rw [ite_eq_right htag,formula_cons,hp]
            have hu : encodeCNF φ ++ encodeCNF ρ = encodeCNF (φ ++ ρ) := by simp [encodeCNF]
            change (if rup (encodeCNF φ ++ encodeCNF ρ,encodeClause c) then [] else [true]) = [] ↔ _
            rw [hu,← hv]
            cases rup (encodeCNF (φ ++ ρ),encodeClause c) <;> decide
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,List.append_eq_nil_iff,rup_run_cons]
          simp only [hnext,Function.iterate_zero_apply]
          exact and_congr hc (ih n hlen)

/-- Check the pinned reverse-unit-propagation learning relation on a
newest-first canonical trace, using measured clause suffix traversal. -/
theorem MeasuredRUPRun :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ ρ : CNF), test (encodeCNF φ,encodeCNF ρ) = true ↔
        IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map fun c => c.toFinset) := by
  obtain ⟨rup,hr,hrs⟩ := MeasuredRUP
  obtain ⟨parse,hp,hjoin,hsem⟩ := measuredFirstClause_reassembles
  have ht : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (tail parse) :=
    cpt_comp (g := fun p : Raw × Raw => p.2) hp cpt_snd
  have hlen (s : Raw) : (tail parse s).length ≤ s.length := by
    have h := congrArg List.length (hjoin s)
    simp only [List.length_append] at h
    unfold tail
    omega
  let rem := fun s => (tail parse)^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hm : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) rem :=
    cpt_iterLen ht hlen cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let bad := fun s => failure parse rup (unpairB (unpairB s).2).1 (rem s)
  have hb : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) bad :=
    failure_cpt hp hr (cpt_unpairB1_1 cpt_unpairB2) hm
  let collect := fun s => (List.range (unpairB s).2.length).flatMap (fun i => bad (pairB (un i) s))
  have hc : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) collect :=
    cpt_flatMapRange hb cpt_unpairB2 cpt_id
  let output := fun s => (collect s).isEmpty
  have ho := cpt_comp (g := fun w : Raw => !w.isEmpty)
    (cpt_sel hc (cpt_const [true]) (cpt_const [])) bf_cpt_neL
  have he : (fun s => !(sel (collect s) [true] []).isEmpty) = output := by
    funext s
    unfold output
    cases collect s <;> rfl
  rw [he] at ho
  refine ⟨fun p => output (pairB p.1 p.2),cpt_comp (g := output) cpt_pairB ho,fun φ ρ => ?_⟩
  simp only [output,collect,bad,rem,unpairB_pairB,un_length,List.isEmpty_iff]
  have h0 : tail parse [] = [] := (List.append_eq_nil_iff.mp (hjoin [])).2
  exact failures_correct parse rup hsem h0 hrs φ ρ _ (formula_count ρ)

end PEqualNP.Outside
