import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredClauseLiteralCount
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

/-- Count clauses of a supplied unary width without materializing any powers of two. -/
theorem MeasuredWidthClassCount :
    ∃ count : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) count ∧
      ∀ (width : List Bool) (φ : CNF),
        count (width,encodeCNF φ) =
          List.replicate ((φ.filter (fun c => c.length = width.length)).length) true := by
  obtain ⟨countL,hL,hlspec⟩ := MeasuredClauseLiteralCount
  let unary := fun x : List Bool => List.replicate x.length true
  have hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) unary := by
    simpa [unary] using L055 Polynomial.X
  let choose := fun z : List Bool × List Bool => if decide (countL z.2 = unary z.1) then [true] else []
  have heq : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  have hc : ComputableInPolyTime encodePair (fun x : List Bool => x) choose :=
    cpt_bitFlag (cpt_comp (cpt_pairG (cpt_comp cpt_snd hL) (cpt_comp cpt_fst hu)) heq)
  obtain ⟨count,hcount,hcspec⟩ := MeasuredClauseMap choose hc
  refine ⟨count,hcount,fun width φ => ?_⟩
  rw [hcspec]
  have hchoose (c : Clause) :
      choose (width, encodeClause c) = if c.length = width.length then [true] else [] := by
    simp [choose, hlspec, unary]
  simp only [hchoose]
  induction φ with
  | nil => simp
  | cons c φ ih =>
      by_cases he : c.length = width.length
      · simp [he, ih, List.replicate_succ]
      · simp [he, ih]

end PEqualNP.Outside
