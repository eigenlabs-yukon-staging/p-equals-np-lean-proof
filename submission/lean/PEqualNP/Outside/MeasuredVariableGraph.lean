import PEqualNP.Outside.CNFComponentCorrect
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredLiteralMap

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search

def setLiteralSign (b : Bool) (w : List Bool) : List Bool := true :: b :: w.tail.tail

theorem setLiteralSign_cpt {f : List Bool → List Bool} (b : Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x => setLiteralSign b (f x)) :=
  cpt_cons1 true (cpt_cons1 b (cpt_tail1 (cpt_tail1 hf)))

theorem setLiteralSign_spec (b : Bool) (l : Literal) :
    setLiteralSign b (encodeLiteral l) = encodeLiteral (l.1,b) := by
  rw [encodeLiteral_eq,encodeLiteral_eq]
  rfl

private def edge (p : List Bool × List Bool) : List Bool :=
  setLiteralSign false p.1 ++ setLiteralSign true p.2 ++ [false,false]

private theorem edge_cpt : ComputableInPolyTime encodePair (fun x : List Bool => x) edge := by
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => edge (unpairB x)) :=
    cpt_app2 (cpt_app2 (setLiteralSign_cpt false cpt_unpairB1) (setLiteralSign_cpt true cpt_unpairB2)) (cpt_const [false,false])
  have h := cpt_comp cpt_pairB hr
  simpa [unpairB_pairB] using h

private theorem edge_literal (l m : Literal) :
    edge (encodeLiteral l,encodeLiteral m) = encodeClause [(l.1,false),(m.1,true)] := by
  simp [edge,setLiteralSign_spec,encodeClause,List.append_assoc]

/-- Measured extraction of the signed binary implications for variable co-occurrence. -/
theorem MeasuredVariableGraph :
    ∃ graph : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) graph ∧
      ∀ φ : CNF, graph (encodeCNF φ) =
        encodeCNF (φ.flatMap (fun c => c.flatMap (fun l => c.map (fun m => [(l.1,false),(m.1,true)])))) := by
  obtain ⟨row,hrow,hrs⟩ := MeasuredLiteralMap edge edge_cpt
  let mkRow := fun p : List Bool × List Bool => row (p.2,p.1)
  have hmr : ComputableInPolyTime encodePair (fun x : List Bool => x) mkRow :=
    cpt_comp (cpt_pairG cpt_snd cpt_fst) hrow
  obtain ⟨matrix,hm,hms⟩ := MeasuredLiteralMap mkRow hmr
  let mkMatrix := fun p : List Bool × List Bool => matrix (p.2,p.2)
  have hmm : ComputableInPolyTime encodePair (fun x : List Bool => x) mkMatrix :=
    cpt_comp (cpt_pairG cpt_snd cpt_snd) hm
  obtain ⟨outer,ho,hos⟩ := MeasuredClauseMap mkMatrix hmm
  let graph := fun w => outer ([],w)
  have hgraph : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) graph :=
    cpt_comp (cpt_pair (cpt_const []) cpt_id) ho
  refine ⟨graph,hgraph,fun φ => ?_⟩
  change outer ([],encodeCNF φ) = _
  rw [hos]
  simp only [mkMatrix,hms,mkRow,hrs,edge_literal]
  simp only [encodeCNF,List.flatMap_assoc,List.flatMap_map,Function.comp_apply]

end PEqualNP.Outside
