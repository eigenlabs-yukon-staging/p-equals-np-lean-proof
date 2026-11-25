import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private theorem no_items (i : ℕ) :
    (dropI^[i] (encodeClause [])).headD false = false := by
  cases i with
  | zero => rfl
  | succ i =>
      rw [Function.iterate_succ_apply]
      change (dropI^[i] []).headD false = false
      induction i with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply,show dropI [] = [] by rfl,ih]

private theorem scan_semantics (f : List Bool → List Bool) (c : Clause)
    (n : ℕ) (hn : c.length ≤ n) :
    (List.range n).flatMap (fun i =>
      let s := dropI^[i] (encodeClause c)
      if s.headD false then f s else []) =
      (List.range c.length).flatMap (fun i => f (encodeClause (c.drop i))) := by
  induction c generalizing n with
  | nil =>
      change _ = ([] : List Bool)
      rw [List.flatMap_eq_nil_iff]
      intro i _
      change (if (dropI^[i] (encodeClause [])).headD false then _ else []) = []
      simp only [no_items,Bool.false_eq_true,ite_false]
  | cons l c ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have hle : c.length ≤ n := by simpa using hn
          have he : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
          have ht : (encodeLiteral l ++ encodeClause c).headD false = true := by simp [encodeLiteral_eq]
          have hs (i : ℕ) : dropI^[i+1] (encodeClause (l :: c)) = dropI^[i] (encodeClause c) := by
            rw [Function.iterate_succ_apply,he,dropI_lit]
          rw [List.length_cons,List.range_succ_eq_map,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_cons,
            List.flatMap_map,List.flatMap_map]
          simp only [hs,Function.iterate_zero_apply]
          change (if (encodeClause (l :: c)).headD false then f (encodeClause (l :: c)) else []) ++
            (List.range n).flatMap (fun i =>
              let s := dropI^[i] (encodeClause c)
              if s.headD false then f s else []) = _
          rw [he,ht,if_pos rfl,ih n hle]
          simp only [List.drop_zero,List.drop_succ_cons,he]

/-- Lift a measured operation with a shared argument over all nonempty
literal suffixes of a canonical clause. -/
theorem MeasuredLiteralSuffixMap (f : List Bool × List Bool → List Bool)
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f) :
    ∃ collect : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) collect ∧
      ∀ (arg : List Bool) (c : Clause),
        collect (arg,encodeClause c) = (List.range c.length).flatMap (fun i => f (arg,encodeClause (c.drop i))) := by
  have hdrop (s : List Bool) : (dropI s).length ≤ s.length := by
    have h := hd_len s
    omega
  let rem := fun s => dropI^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) rem :=
    cpt_iterLen cpt_dropI hdrop cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let branch := fun s => if (rem s).headD false then
    f ((unpairB (unpairB s).2).1,rem s) else []
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) branch := by
    refine cptE (cpt_sel (cpt_hd1 hr) (cpt_const [])
      (cpt_comp (cpt_pair (cpt_unpairB1_1 cpt_unpairB2) hr) hf)) (fun s => ?_)
    change sel (hd (rem s)) [] (f ((unpairB (unpairB s).2).1,rem s)) = branch s
    unfold branch
    cases rem s with
    | nil => rfl
    | cons a r => cases a <;> rfl
  let raw := fun s => (List.range (unpairB s).2.length).flatMap (fun i => branch (pairB (un i) s))
  have hraw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_flatMapRange hb cpt_unpairB2 cpt_id
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp (g := raw) cpt_pairB hraw,fun arg c => ?_⟩
  simp only [raw,branch,rem,unpairB_pairB,un_length]
  apply scan_semantics (fun w => f (arg,w))
  have hl := length_le_flatMap_lit c
  simp only [encodeClause,List.length_append]
  omega

end PEqualNP.Outside
