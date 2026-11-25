import PEqualNP.Outside.MeasuredClauseSetEquality
import PEqualNP.Outside.MeasuredClauseMap

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

/-- Return the entries of a supplied universe that occur as finite-set clauses
in the candidate formula, preserving the universe's order and multiplicities. -/
theorem MeasuredCNFIntersection :
    ∃ intersect : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) intersect ∧
      ∀ (φ U : CNF), intersect (encodeCNF φ,encodeCNF U) =
        encodeCNF (U.filter (fun c => decide (∃ d ∈ φ, d.toFinset = c.toFinset))) := by
  obtain ⟨test,ht,hts⟩ := MeasuredClauseSetEquality
  let mark := fun p : Raw × Raw => if test (p.2,p.1) then [true] else []
  have hm : ComputableInPolyTime encodePair (fun x : Raw => x) mark := by
    have h := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB2 cpt_unpairB1) ht)
    simpa only [unpairB_pairB,mark] using cpt_comp cpt_pairB h
  obtain ⟨scan,hs,hss⟩ := MeasuredClauseMap mark hm
  let keep := fun p : Raw × Raw => sel (scan (p.2,p.1)) [] p.2
  have hk : ComputableInPolyTime encodePair (fun x : Raw => x) keep := by
    have h := cpt_sel (cpt_comp (cpt_pair cpt_unpairB2 cpt_unpairB1) hs) (cpt_const []) cpt_unpairB2
    simpa only [unpairB_pairB,keep] using cpt_comp cpt_pairB h
  obtain ⟨intersect,hi,his⟩ := MeasuredClauseMap keep hk
  refine ⟨intersect,hi,fun φ U => ?_⟩
  rw [his]
  have one (c : Clause) : keep (encodeCNF φ,encodeClause c) =
      if ∃ d ∈ φ, d.toFinset = c.toFinset then encodeClause c else [] := by
    unfold keep
    rw [hss]
    have hm' (d : Clause) : mark (encodeClause c,encodeClause d) =
        if d.toFinset = c.toFinset then [true] else [] := by
      unfold mark
      by_cases h : d.toFinset = c.toFinset
      · simp [h,hts _ _ |>.2 h]
      · have hf : test (encodeClause d,encodeClause c) = false := Bool.eq_false_iff.mpr (fun h' => h ((hts _ _).1 h'))
        simp [h,hf]
    simp only [hm']
    have he : (φ.flatMap (fun d => if d.toFinset = c.toFinset then [true] else [])) = [] ↔
        ¬ ∃ d ∈ φ, d.toFinset = c.toFinset := by
      rw [List.flatMap_eq_nil_iff]
      simp [not_exists]
    by_cases h : ∃ d ∈ φ, d.toFinset = c.toFinset
    · have hn := fun e => (he.mp e) h
      cases hList : φ.flatMap (fun d => if d.toFinset = c.toFinset then [true] else []) with
      | nil => exact False.elim (hn hList)
      | cons a as => simp [sel,h]
    · rw [he.mpr h]
      simp [sel,h]
  simp only [one]
  induction U with
  | nil => rfl
  | cons c U ih =>
    by_cases h : ∃ d ∈ φ, d.toFinset = c.toFinset <;> simp [encodeCNF,h] at ih ⊢ <;> simp [ih]

end PEqualNP.Outside
