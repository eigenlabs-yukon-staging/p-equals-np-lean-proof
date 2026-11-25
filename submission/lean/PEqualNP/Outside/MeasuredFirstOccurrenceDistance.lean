import PEqualNP.Outside.MeasuredFirstOccurrenceIndex
import PEqualNP.Library.Machines.LenLE

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search

private abbrev Raw := List Bool

/-- Mark a violation of a fixed directional distance bound between the
first occurrences of two variable identifiers in a literal sequence. -/
theorem MeasuredFirstOccurrenceDistance (k : ℕ) :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    ∃ mark : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mark ∧
      ∀ (c : Clause) (l m : Literal),
        mark (pair (encodeClause c) (pair (encodeLiteral l) (encodeLiteral m))) =
          if (c.map Prod.fst).idxOf l.1 ≤ (c.map Prod.fst).idxOf m.1 + k then [] else [true] := by
  dsimp only
  obtain ⟨index,hi,his⟩ := MeasuredFirstOccurrenceIndex
  let packedIndex := fun s : Raw => pairB
    (index ((unpairB (unpairB s).2).2,(unpairB s).1) ++ List.replicate k true)
    (index ((unpairB (unpairB s).2).1,(unpairB s).1))
  let good := fun s : Raw => decide ((unpairB (packedIndex s)).2.length ≤ (unpairB (packedIndex s)).1.length)
  let mark := fun s : Raw => sel (bflag (good s)) [true] []
  have hL := cpt_comp (cpt_pair (cpt_unpairB1_1 cpt_unpairB2) cpt_unpairB1) hi
  have hR := cpt_comp (cpt_pair (cpt_unpairB2_1 cpt_unpairB2) cpt_unpairB1) hi
  have hP : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) packedIndex :=
    cpt_pairB2 (cpt_app2 hR (cpt_const (List.replicate k true))) hL
  have hCmp := cpt_comp (cpt_pair (cpt_unpairB1_1 hP) (cpt_unpairB2_1 hP)) LenCmp.lenLE_polyTime
  have hm : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) mark :=
    cpt_sel (cpt_bitFlag hCmp) (cpt_const [true]) (cpt_const [])
  refine ⟨mark,hm,fun c l m => ?_⟩
  change mark (pairB (encodeClause c) (pairB (encodeLiteral l) (encodeLiteral m))) = _
  simp only [mark,good,packedIndex,unpairB_pairB,his,List.length_append,List.length_replicate]
  by_cases h : (c.map Prod.fst).idxOf l.1 ≤ (c.map Prod.fst).idxOf m.1 + k <;> simp [h,bflag,sel]

end PEqualNP.Outside
