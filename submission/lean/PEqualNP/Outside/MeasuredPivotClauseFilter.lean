import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Search

private abbrev Raw := List Bool

private def selectFlag (want : Bool) (flag yes : Raw) : Raw :=
  if want then sel flag [] yes else sel flag yes []

private theorem selectFlag_cpt (want : Bool) {f g : Raw → Raw}
    (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f)
    (hg : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) g) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => selectFlag want (f s) (g s)) := by
  cases want
  · exact cpt_sel hf hg (cpt_const [])
  · exact cpt_sel hf (cpt_const []) hg

private def choose (p n : Bool) (z : Raw × Raw) : Raw :=
  selectFlag p (bflag (memB z.1 z.2))
    (selectFlag n (bflag (memB (negI z.1) z.2)) z.2)

private theorem choose_cpt (p n : Bool) :
    ComputableInPolyTime encodePair (fun x : Raw => x) (choose p n) := by
  have hm := cpt_memB cpt_unpairB1 cpt_unpairB2
  have hn := cpt_memB (cpt_negI cpt_unpairB1) cpt_unpairB2
  have h : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => choose p n (unpairB s)) :=
    selectFlag_cpt p hm (selectFlag_cpt n hn cpt_unpairB2)
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

private theorem select_lit (x : ℕ) (c : Clause) (p n : Bool) :
    choose p n (encodeLiteral (x,true),encodeClause c) =
      if decide ((x,true) ∈ c) = p ∧ decide ((x,false) ∈ c) = n then encodeClause c else [] := by
  have hp : memB (encodeLiteral (x,true)) (encodeClause c) = decide ((x,true) ∈ c) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using literal_mem_code (x,true) c)
  have hn : memB (encodeLiteral (x,false)) (encodeClause c) = decide ((x,false) ∈ c) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using literal_mem_code (x,false) c)
  simp only [choose,negI_lit,show neg (x,true) = (x,false) by rfl,hp,hn]
  cases p <;> cases n <;> by_cases ha : (x,true) ∈ c <;> by_cases hb : (x,false) ∈ c <;>
    simp [selectFlag,bflag,sel,ha,hb]

/-- Filter canonical clauses by exact presence of the positive and
negative literals of a supplied variable. -/
theorem MeasuredPivotClauseFilter (p n : Bool) :
    ∃ pick : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) pick ∧
      ∀ (x : ℕ) (φ : CNF), pick (encodeLiteral (x,true),encodeCNF φ) =
        encodeCNF (φ.filter (fun c => decide (decide ((x,true) ∈ c) = p ∧ decide ((x,false) ∈ c) = n))) := by
  obtain ⟨pick,hp,hs⟩ := MeasuredClauseMap (choose p n) (choose_cpt p n)
  refine ⟨pick,hp,fun x φ => ?_⟩
  rw [hs]
  simp only [select_lit]
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      by_cases h : decide ((x,true) ∈ c) = p ∧ decide ((x,false) ∈ c) = n <;>
        simp [h,encodeCNF] at ih ⊢ <;> first | exact ih | exact congrArg (fun u => encodeClause c ++ u) ih

end PEqualNP.Outside
