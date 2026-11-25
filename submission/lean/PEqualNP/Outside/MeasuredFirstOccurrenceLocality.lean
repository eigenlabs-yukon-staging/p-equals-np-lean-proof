import PEqualNP.Outside.MeasuredFirstOccurrenceDistance
import PEqualNP.Outside.MeasuredVariableOrderCode
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search
open PEqualNP.Library.SearchHelpers.KSat.Hard

private abbrev Raw := List Bool

/-- Check the directional first-occurrence bound for every ordered pair
of literals from the same clause of a canonical formula. -/
theorem MeasuredFirstOccurrenceLocality (k : ℕ) :
    ∃ test : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test ∧
      ∀ φ : CNF, test (encodeCNF φ) = true ↔
        let order := φ.flatten.map Prod.fst
        ∀ c ∈ φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k := by
  obtain ⟨mark,hm,hms⟩ := MeasuredFirstOccurrenceDistance k
  obtain ⟨normalize,hn,hns⟩ := MeasuredVariableOrderCode
  let markPair := fun p : Raw × Raw => mark (pairB (unpairB p.1).1 (pairB (unpairB p.1).2 p.2))
  have hp : ComputableInPolyTime encodePair (fun x : Raw => x) markPair := by
    have h := cpt_comp (cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB1)
      (cpt_pairB2 (cpt_unpairB2_1 cpt_unpairB1) cpt_unpairB2)) hm
    simpa only [unpairB_pairB,markPair] using cpt_comp cpt_pairB h
  obtain ⟨scanRight,hr,hrs⟩ := MeasuredLiteralMap markPair hp
  let markLeft := fun p : Raw × Raw => scanRight (pairB (unpairB p.1).1 p.2,(unpairB p.1).2)
  have hl : ComputableInPolyTime encodePair (fun x : Raw => x) markLeft := by
    have h := cpt_comp (cpt_pair (cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB1) cpt_unpairB2)
      (cpt_unpairB2_1 cpt_unpairB1)) hr
    simpa only [unpairB_pairB,markLeft] using cpt_comp cpt_pairB h
  obtain ⟨scanLeft,ha,has⟩ := MeasuredLiteralMap markLeft hl
  let markClause := fun p : Raw × Raw => scanLeft (pairB p.1 p.2,p.2)
  have hc : ComputableInPolyTime encodePair (fun x : Raw => x) markClause := by
    have h := cpt_comp (cpt_pair (cpt_pairB2 cpt_unpairB1 cpt_unpairB2) cpt_unpairB2) ha
    simpa only [unpairB_pairB,markClause] using cpt_comp cpt_pairB h
  obtain ⟨scan,hf,hfs⟩ := MeasuredClauseMap markClause hc
  let word := fun s : Raw => scan (normalize s,s)
  let test := fun s : Raw => (word s).isEmpty
  have hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) word :=
    cpt_comp (cpt_pair hn cpt_id) hf
  have htest : ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool test := by
    have hne := cpt_comp (g := fun x : Raw => !x.isEmpty) hw bf_cpt_neL
    have hnot := cpt_sel (cpt_bitFlag hne) (cpt_const [true]) (cpt_const [])
    have hem := cpt_comp (g := fun x : Raw => !x.isEmpty) hnot bf_cpt_neL
    have he : (fun s : Raw => !(sel (if !(word s).isEmpty then [true] else []) [true] []).isEmpty) = test := by
      funext s
      unfold test
      cases (word s).isEmpty <;> rfl
    rw [← he]
    exact hem
  refine ⟨test,htest,fun φ => ?_⟩
  let order := φ.flatten.map Prod.fst
  let orderClause := φ.flatten.map (fun l => (l.1,true))
  have hNormal : normalize (encodeCNF φ) = encodeClause orderClause := hns φ
  have hOrder : orderClause.map Prod.fst = order := by simp [orderClause,order,List.map_map,Function.comp_def]
  have hpure (l m : Literal) :
      markPair (pairB (encodeClause orderClause) (encodeLiteral l),encodeLiteral m) =
        if order.idxOf l.1 ≤ order.idxOf m.1 + k then [] else [true] := by
    dsimp only [markPair]
    rw [unpairB_pairB]
    have h := hms orderClause l m
    change mark (pairB (encodeClause orderClause) (pairB (encodeLiteral l) (encodeLiteral m))) =
      (if (orderClause.map Prod.fst).idxOf l.1 ≤ (orderClause.map Prod.fst).idxOf m.1 + k then [] else [true]) at h
    exact h.trans (by rw [hOrder])
  have hleft (c : Clause) (l : Literal) :
      markLeft (pairB (encodeClause orderClause) (encodeClause c),encodeLiteral l) =
        c.flatMap (fun m => if order.idxOf l.1 ≤ order.idxOf m.1 + k then [] else [true]) := by
    simp only [markLeft,unpairB_pairB,hrs,hpure]
  have hclause (c : Clause) :
      markClause (encodeClause orderClause,encodeClause c) =
        c.flatMap (fun l => c.flatMap (fun m => if order.idxOf l.1 ≤ order.idxOf m.1 + k then [] else [true])) := by
    simp only [markClause,has,hleft]
  change (word (encodeCNF φ)).isEmpty = true ↔
    ∀ c ∈ φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k
  simp only [word,hNormal,hfs,hclause,List.isEmpty_iff,List.flatMap_eq_nil_iff]
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro l
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro m
  apply imp_congr_right
  intro _
  by_cases h : order.idxOf l.1 ≤ order.idxOf m.1 + k
  · simp only [if_pos h,h] <;> simp
  · simp only [if_neg h,h,List.cons_ne_nil] <;> simp

end PEqualNP.Outside
