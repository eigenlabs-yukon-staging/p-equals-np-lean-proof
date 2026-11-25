import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private def dupAt (w : List Bool) : Bool :=
  w.headD false && (memB (headI w) (dropI w) || memB (negI (headI w)) (dropI w))

private theorem dupAt_cpt : ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun w => bflag (dupAt w)) := by
  have hm := cpt_memB cpt_headI cpt_dropI
  have hn := cpt_memB (cpt_negI cpt_headI) cpt_dropI
  refine cptE (cpt_sel (cpt_hd1 cpt_id) (cpt_const []) (cpt_sel hm hn (cpt_const [true]))) (fun s => ?_)
  change sel (hd s) [] (sel (bflag (memB (headI s) (dropI s)))
    (bflag (memB (negI (headI s)) (dropI s))) [true]) = _
  cases s with
  | nil => rfl
  | cons b s =>
      cases b <;> cases hm : memB (headI (_ :: s)) (dropI (_ :: s)) <;>
        cases hn : memB (negI (headI (_ :: s))) (dropI (_ :: s)) <;>
        simp [dupAt,sel,hd,bflag,hm,hn]

private theorem dup_cons (l : Literal) (c : Clause) :
    dupAt (encodeClause (l :: c)) = true ↔ l.1 ∈ c.map Prod.fst := by
  have he : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
  rw [he]
  unfold dupAt
  rw [headI_lit,dropI_lit,negI_lit]
  have ht : (encodeLiteral l ++ encodeClause c).headD false = true := by simp [encodeLiteral_eq]
  rw [ht,Bool.true_and,Bool.or_eq_true,literal_mem_code,literal_mem_code]
  obtain ⟨i,b⟩ := l
  constructor
  · rintro (h | h)
    · exact List.mem_map.mpr ⟨(i,b),h,rfl⟩
    · exact List.mem_map.mpr ⟨neg (i,b),h,rfl⟩
  · intro h
    obtain ⟨⟨j,a⟩,ha,hj⟩ := List.mem_map.mp h
    change j = i at hj
    subst j
    cases b <;> cases a <;> simp_all [neg]

private theorem dup_range (c : Clause) (n : ℕ) (hn : c.length ≤ n) :
    ((List.range n).flatMap (fun i => bflag (dupAt (dropI^[i] (encodeClause c)))) = []) ↔
      (c.map Prod.fst).Nodup := by
  induction c generalizing n with
  | nil =>
      suffices h : ∀ i, dupAt (dropI^[i] (encodeClause [])) = false by simp [h,bflag]
      intro i
      cases i with
      | zero => rfl
      | succ i =>
          rw [Function.iterate_succ_apply]
          change dupAt (dropI^[i] []) = false
          induction i with
          | zero => rfl
          | succ i ih => rw [Function.iterate_succ_apply,show dropI [] = [] by rfl,ih]
  | cons l c ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have htail : c.length ≤ n := by simpa using hn
          have hu : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,List.append_eq_nil_iff]
          have he (i : ℕ) :
              dropI^[i+1] (encodeClause (l :: c)) = dropI^[i] (encodeClause c) := by
            rw [Function.iterate_succ_apply,hu,dropI_lit]
          simp only [Function.iterate_zero_apply,he,ih n htail,List.map_cons,List.nodup_cons]
          have hb : bflag (dupAt (encodeClause (l :: c))) = [] ↔ l.1 ∉ c.map Prod.fst := by
            have ht := dup_cons l c
            cases h : dupAt (encodeClause (l :: c)) <;> simp_all [bflag]
          rw [hb]

/-- Detects whether each clause of a canonical CNF uses distinct variables. -/
theorem MeasuredDistinctClauseVariables :
    ∃ test : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test ∧
      ∀ φ : CNF, test (encodeCNF φ) = true ↔ ∀ c ∈ φ, (c.map Prod.fst).Nodup := by
  have hdrop (s : List Bool) : (dropI s).length ≤ s.length := by
    have h := hd_len s
    omega
  let item := fun s : List Bool => bflag (dupAt (dropI^[(unpairB s).1.length] (unpairB s).2))
  have hi : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) item :=
    cpt_comp (g := fun w => bflag (dupAt w)) (cpt_iterLen cpt_dropI hdrop cpt_unpairB1 cpt_unpairB2) dupAt_cpt
  let onClause := fun w : List Bool => (List.range w.length).flatMap (fun i => item (pairB (un i) w))
  have ho : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) onClause :=
    cpt_flatMapRange hi cpt_id cpt_id
  obtain ⟨collect,hc,hcs⟩ := MeasuredClauseMap
    (fun z => onClause z.2) (cpt_comp cpt_snd ho)
  let out := fun x => collect ([],x)
  have hct := cpt_comp (cpt_pair (cpt_const []) cpt_id) hc
  have ht := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_sel hct (cpt_const [true]) (cpt_const [])) bf_cpt_neL
  have he : (fun x => !(sel (out x) [true] []).isEmpty) = (fun x => (out x).isEmpty) := by
    funext x
    cases out x <;> rfl
  change ComputableInPolyTime _ _ (fun x => !(sel (out x) [true] []).isEmpty) at ht
  rw [he] at ht
  refine ⟨_,ht,fun φ => ?_⟩
  change (collect ([],encodeCNF φ)).isEmpty = true ↔ _
  rw [List.isEmpty_iff,hcs,List.flatMap_eq_nil_iff]
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro _
  simp only [onClause,item,unpairB_pairB,un_length]
  apply dup_range
  have h := length_le_flatMap_lit c
  simp only [encodeClause,List.length_append]
  omega

end PEqualNP.Outside
