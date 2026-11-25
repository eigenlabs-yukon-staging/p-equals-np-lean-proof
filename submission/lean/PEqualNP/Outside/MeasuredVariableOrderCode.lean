import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

private def positiveCode (s : Raw) : Raw :=
  sel (hd s.tail) (negI s) s

private theorem positive_cpt :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) positiveCode :=
  cpt_sel (cpt_comp cpt_tail cpt_hd) (cpt_negI cpt_id) cpt_id

private theorem positive_code (l : Literal) :
    positiveCode (encodeLiteral l) = encodeLiteral (l.1,true) := by
  rcases l with ⟨x,b⟩
  cases b
  · have h : hd (encodeLiteral (x,false)).tail = [] := rfl
    simp [positiveCode,h,sel,negI_lit,neg]
  · have h : hd (encodeLiteral (x,true)).tail ≠ [] := by simp [hd,encodeLiteral]
    simp [positiveCode,h,sel]

/-- Collect variable identifiers in clause order and encode them as one
positive clause. Each identifier is preserved independently of its sign. -/
theorem MeasuredVariableOrderCode :
    ∃ normalize : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) normalize ∧
      ∀ φ : CNF, normalize (encodeCNF φ) =
        encodeClause ((φ.flatten).map (fun l => (l.1,true))) := by
  let one := fun p : Raw × Raw => positiveCode p.2
  have hOne : ComputableInPolyTime encodePair (fun x : Raw => x) one := by
    have h := cpt_comp cpt_pairB (cpt_comp cpt_unpairB2 positive_cpt)
    simpa only [unpairB_pairB,one] using h
  obtain ⟨mapLit,hLit,hLitSpec⟩ := MeasuredLiteralMap one hOne
  let clause := fun p : Raw × Raw => mapLit ([],p.2)
  have hClause : ComputableInPolyTime encodePair (fun x : Raw => x) clause := by
    have h := cpt_comp cpt_pairB (cpt_comp (cpt_pair (cpt_const []) cpt_unpairB2) hLit)
    simpa only [unpairB_pairB,clause] using h
  obtain ⟨mapClause,hc,hcs⟩ := MeasuredClauseMap clause hClause
  refine ⟨fun x => mapClause ([],x) ++ [false,false],
    cpt_app2 (cpt_comp (cpt_pair (cpt_const []) cpt_id) hc) (cpt_const [false,false]),fun φ => ?_⟩
  change mapClause ([],encodeCNF φ) ++ [false,false] = _
  rw [hcs]
  have hmap (c : Clause) : clause ([],encodeClause c) =
      c.flatMap (fun l => encodeLiteral (l.1,true)) := by
    simp only [clause,hLitSpec,one,positive_code]
  simp only [encodeClause,List.flatMap_map]
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.flatten_cons,List.flatMap_append,List.append_assoc]
    rw [ih]
    exact congrArg (fun p => p ++ ((cs.flatten).flatMap (fun a => encodeLiteral (a.1,true)) ++ [false,false])) (hmap c)

end PEqualNP.Outside
