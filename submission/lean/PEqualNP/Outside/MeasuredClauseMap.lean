import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private theorem code_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]

private theorem formula_length (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.length_cons,code_cons,List.length_append]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

private theorem range_semantics
    (split : List Bool → List Bool × List Bool)
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (h0 : (split []).2 = [])
    (f : List Bool × List Bool → List Bool) (arg : List Bool)
    (φ : CNF) (n : ℕ) (hn : φ.length ≤ n) :
    (List.range n).flatMap (fun i =>
      let rem := (fun s => (split s).2)^[i] (encodeCNF φ)
      if rem = [] then [] else f (arg,(split rem).1)) =
      φ.flatMap (fun c => f (arg,encodeClause c)) := by
  induction φ generalizing n with
  | nil =>
      change _ = ([] : List Bool)
      rw [List.flatMap_eq_nil_iff]
      intro i _
      clear * - split h0 i
      have h : (fun s => (split s).2)^[i] ([] : List Bool) = [] := by
        induction i with
        | zero => rfl
        | succ i ih => rw [Function.iterate_succ_apply,h0,ih]
      change (if (fun s => (split s).2)^[i] ([] : List Bool) = [] then [] else _) = []
      rw [h]
      rfl
  | cons c φ ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have htail : φ.length ≤ n := by simpa using hn
          have he : encodeCNF (c :: φ) ≠ [] := by rw [code_cons]; simp [encodeClause]
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          have hnext (i : ℕ) : (fun s => (split s).2)^[i+1] (encodeCNF (c :: φ)) =
              (fun s => (split s).2)^[i] (encodeCNF φ) := by
            rw [Function.iterate_succ_apply,code_cons]
            simp only [hs]
          simp only [hnext,Function.iterate_zero_apply]
          change (if encodeCNF (c :: φ) = [] then [] else f (arg,(split (encodeCNF (c :: φ))).1)) ++
            (List.range n).flatMap (fun i =>
              let rem := (fun s => (split s).2)^[i] (encodeCNF φ)
              if rem = [] then [] else f (arg,(split rem).1)) = _
          rw [ite_eq_right he,code_cons,hs,ih n htail]
          rfl

/-- A measured transformer on a clause and a shared argument lifts to measured
concatenation over all clauses of a canonical CNF. -/
theorem MeasuredClauseMap (f : List Bool × List Bool → List Bool)
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f) :
    ∃ collect : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) collect ∧
      ∀ (arg : List Bool) (φ : CNF),
        collect (arg,encodeCNF φ) = φ.flatMap (fun c => f (arg,encodeClause c)) := by
  obtain ⟨split,hs,hjoin,hsem⟩ := measuredFirstClause_reassembles
  let tail := fun s => (split s).2
  have ht : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) tail :=
    cpt_comp hs cpt_snd
  have hlen (s : List Bool) : (tail s).length ≤ s.length := by
    have h := congrArg List.length (hjoin s)
    simp only [List.length_append] at h
    dsimp only [tail]
    omega
  let rem := fun s => tail^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) rem :=
    cpt_iterLen ht hlen cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let branch := fun s => if rem s = [] then [] else f ((unpairB (unpairB s).2).1,(split (rem s)).1)
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) branch :=
    cpt_sel hr (cpt_const []) (cpt_comp (cpt_pair (cpt_unpairB1_1 cpt_unpairB2)
      (cpt_comp (cpt_comp hr hs) cpt_fst)) hf)
  let raw := fun s => (List.range (unpairB s).2.length).flatMap (fun i => branch (pairB (un i) s))
  have hraw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_flatMapRange hb cpt_unpairB2 cpt_id
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp (g := raw) cpt_pairB hraw,fun arg φ => ?_⟩
  simp only [raw,branch,rem,tail,unpairB_pairB,un_length]
  exact range_semantics split hsem (List.append_eq_nil_iff.mp (hjoin [])).2 f arg φ _ (formula_length φ)

end PEqualNP.Outside
