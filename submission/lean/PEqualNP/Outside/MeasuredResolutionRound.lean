import PEqualNP.Outside.MeasuredResolutionLine
import PEqualNP.Outside.BoundedResolutionSaturation

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private abbrev Raw := List Bool

private theorem filter_emit (L : CNF) (p : Clause → Prop) :
    L.flatMap (fun c => @ite _ (p c) (Classical.propDecidable _) (encodeClause c) []) =
    encodeCNF (L.filter (fun c => @decide (p c) (Classical.propDecidable _))) := by
  classical
  induction L with
  | nil => rfl
  | cons c L ih =>
      by_cases h : p c <;> simp [h,encodeCNF] at ih ⊢ <;>
        first | exact ih | exact congrArg (fun r => encodeClause c ++ r) ih

/-- A measured saturation round retains exactly those clauses of the fixed
universe that can be written as axioms or resolved from the previous round. -/
theorem MeasuredResolutionRound :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    ∃ advance : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) advance ∧
      ∀ φ U old : CNF, advance (pair (encodeCNF φ) (pair (encodeCNF U) (encodeCNF old))) =
        encodeCNF (U.filter (fun c => @decide
          ((∃ a ∈ φ, a.toFinset = c.toFinset) ∨
            ∃ a ∈ old, ∃ b ∈ old, PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset)
          (Classical.propDecidable _))) := by
  classical
  obtain ⟨query,hq,hqs⟩ := MeasuredResolutionLine
  let keep := fun z : Raw × Raw =>
    sel (if query (pairB (unpairB z.1).1 (pairB (unpairB z.1).2 z.2)) then [true] else []) [] z.2
  have hk : ComputableInPolyTime encodePair (fun x : Raw => x) keep := by
    have h := cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB1)
      (cpt_pairB2 (cpt_unpairB2_1 cpt_unpairB1) cpt_unpairB2)
    have hw := cpt_comp cpt_pairB (cpt_sel (cpt_bitFlag (cpt_comp h hq)) (cpt_const []) cpt_unpairB2)
    simpa only [unpairB_pairB,keep] using hw
  obtain ⟨collect,hc,hcs⟩ := MeasuredClauseMap keep hk
  let advance := fun s => collect (pairB (unpairB s).1 (unpairB (unpairB s).2).2,(unpairB (unpairB s).2).1)
  have h := cpt_comp (cpt_pair (cpt_pairB2 cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2))
    (cpt_unpairB1_1 cpt_unpairB2)) hc
  refine ⟨advance,h,fun φ U old => ?_⟩
  change advance (pairB (encodeCNF φ) (pairB (encodeCNF U) (encodeCNF old))) =
    encodeCNF (resolutionRound φ U old)
  simp only [advance,unpairB_pairB,hcs]
  have hrow (c : Clause) : keep (pairB (encodeCNF φ) (encodeCNF old),encodeClause c) =
      @ite _ (resolutionLine φ old c) (Classical.propDecidable _) (encodeClause c) [] := by
    have hv : query (pairB (encodeCNF φ) (pairB (encodeCNF old) (encodeClause c))) = true ↔
        resolutionLine φ old c := hqs φ old c
    simp only [keep,unpairB_pairB]
    by_cases hx : resolutionLine φ old c
    · simp [sel,hv.mpr hx,hx]
    · have hy : query (pairB (encodeCNF φ) (pairB (encodeCNF old) (encodeClause c))) = false := by
        cases hq' : query (pairB (encodeCNF φ) (pairB (encodeCNF old) (encodeClause c))) with
        | false => rfl
        | true => exact (hx (hv.mp hq')).elim
      simp [sel,hy,hx]
  simp only [hrow]
  exact filter_emit U _

end PEqualNP.Outside
