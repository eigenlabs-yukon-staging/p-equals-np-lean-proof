import PEqualNP.Outside.MeasuredClauseSetEquality
import PEqualNP.Defs.ProofComplexity
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

private theorem erased_set (c : Clause) (l : Literal) :
    (c.filter (fun m => decide (m ≠ l))).toFinset = c.toFinset.erase l := by
  ext m
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_erase]
  exact and_comm

private theorem resolvent_iff (a b c : Clause) :
    PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset ↔
      ∃ l ∈ a, l.2 = true ∧ neg l ∈ b ∧ c.toFinset =
        ((a.filter (fun m => decide (m ≠ l))) ++ (b.filter (fun m => decide (m ≠ neg l)))).toFinset := by
  simp only [PEqualNP.ProofComplexity.IsResolvent,List.mem_toFinset,List.toFinset_append,erased_set]
  constructor
  · rintro ⟨v,ha,hb,hc⟩
    exact ⟨(v,true),ha,rfl,hb,hc⟩
  · rintro ⟨⟨v,s⟩,ha,hs,hb,hc⟩
    change s = true at hs
    subst s
    exact ⟨v,ha,hb,hc⟩

private def firstClause (s : Raw) := (unpairB s).1
private def secondClause (s : Raw) := (unpairB (unpairB s).2).1
private def thirdClause (s : Raw) := (unpairB (unpairB s).2).2

private def resolvePayload (erase : Raw × Raw → Raw) (clauses pivot : Raw) : Raw :=
  erase (pivot,firstClause clauses) ++ erase (negI pivot,secondClause clauses) ++ [false,false]

private def pivotFlags (erase : Raw × Raw → Raw) (eq : Raw × Raw → Bool) (p : Raw × Raw) : Raw :=
  sel (hd p.2.tail) []
    (sel (bflag (memB (negI p.2) (secondClause p.1))) []
      (bflag (eq (thirdClause p.1,resolvePayload erase p.1 p.2))))

private theorem pivotFlags_cpt {erase : Raw × Raw → Raw}
    {eq : Raw × Raw → Bool}
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hq : ComputableInPolyTime encodePair Computability.encodeBool eq) :
    ComputableInPolyTime encodePair (fun x : Raw => x) (pivotFlags erase eq) := by
  have hc := cpt_unpairB1
  have hl := cpt_unpairB2
  have hb := cpt_unpairB2_1 hc
  have hca := cpt_unpairB1_1 hc
  have hcb := cpt_unpairB1_1 hb
  have hcc := cpt_unpairB2_1 hb
  have hn := cpt_negI hl
  have hm := cpt_memB hn hcb
  have hs := cpt_hd1 (cpt_tail1 hl)
  have h1 := cpt_comp (cpt_pair hl hca) he
  have h2 := cpt_comp (cpt_pair hn hcb) he
  have hr := cpt_app2 (cpt_app2 h1 h2) (cpt_const [false,false])
  have hflag : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x)
      (fun s => pivotFlags erase eq (unpairB s)) :=
    cpt_sel hs (cpt_const []) (cpt_sel hm (cpt_const []) (cpt_bitFlag (cpt_comp (cpt_pair hcc hr) hq)))
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB hflag

/-- Test an exact resolution step over canonical parent and candidate
clauses by enumerating positive parent pivots and comparing finite sets. -/
theorem MeasuredResolutionStep :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    ∃ test : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test ∧
      ∀ a b c : Clause,
        test (pair (encodeClause a) (pair (encodeClause b) (encodeClause c))) = true ↔
          PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset := by
  classical
  obtain ⟨erase,he,hes⟩ := measuredLiteralPayloadErase
  obtain ⟨eq,hq,hqs⟩ := MeasuredClauseSetEquality
  obtain ⟨scan,hs,hss⟩ := MeasuredLiteralMap _ (pivotFlags_cpt he hq)
  let test := fun x => !(scan (x,firstClause x)).isEmpty
  have ht : ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool test :=
    cpt_comp (g := fun x : Raw => !x.isEmpty) (cpt_comp (cpt_pair cpt_id cpt_unpairB1) hs) bf_cpt_neL
  refine ⟨test,ht,fun a b c => ?_⟩
  let s := pairB (encodeClause a) (pairB (encodeClause b) (encodeClause c))
  have hproj : firstClause s = encodeClause a ∧ secondClause s = encodeClause b ∧ thirdClause s = encodeClause c := by
    simp [s,firstClause,secondClause,thirdClause,unpairB_pairB]
  have hp (l : Literal) :
      pivotFlags erase eq (s,encodeLiteral l) ≠ [] ↔ l.2 = true ∧ neg l ∈ b ∧ c.toFinset =
        ((a.filter (fun m => decide (m ≠ l))) ++ (b.filter (fun m => decide (m ≠ neg l)))).toFinset := by
    let res := (a.filter (fun m => decide (m ≠ l))) ++ (b.filter (fun m => decide (m ≠ neg l)))
    have hres : resolvePayload erase s (encodeLiteral l) = encodeClause res := by
      simp only [resolvePayload,hproj.1,hproj.2.1,negI_lit,hes]
      simp only [res,encodeClause,List.flatMap_append]
    have hpivot : hd (encodeLiteral l).tail = [] ↔ l.2 = false := by
      rw [encodeLiteral_eq]
      cases l.2 <;> simp [hd]
    have hm := literal_mem_code (neg l) b
    have hv := hqs c res
    change pivotFlags erase eq (s,encodeLiteral l) ≠ [] ↔ _ ∧ _ ∧ c.toFinset = res.toFinset
    simp only [pivotFlags,sel,hproj.2.1,hproj.2.2,hres,hpivot,negI_lit,← hm,← hv]
    cases l.2 <;> cases memB (encodeLiteral (neg l)) (encodeClause b) <;>
      cases eq (encodeClause c,encodeClause res) <;> decide
  change (!(scan (s,firstClause s)).isEmpty) = true ↔ _
  simp only [hproj.1,hss,Bool.not_eq_true',List.isEmpty_eq_false_iff,ne_eq,List.flatMap_eq_nil_iff]
  push Not
  rw [resolvent_iff]
  exact exists_congr (fun l => and_congr_right (fun _ => hp l))

end PEqualNP.Outside
