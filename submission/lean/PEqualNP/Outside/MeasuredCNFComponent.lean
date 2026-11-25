import PEqualNP.Outside.MeasuredVariableGraph
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search
open PEqualNP.Library.SearchHelpers.Tab.StepW

private def keep (p : List Bool × List Bool) : List Bool :=
  if p.2.headD false then
    if memB (setLiteralSign true (headI p.2)) p.1 then p.2 else []
  else []

private theorem keep_cpt : ComputableInPolyTime encodePair (fun x : List Bool => x) keep := by
  have hh := cpt_comp cpt_unpairB2 cpt_headI
  have hm := cpt_memB (setLiteralSign_cpt true hh) cpt_unpairB1
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => keep (unpairB s)) := by
    refine cptE (cpt_sel (cpt_hd1 cpt_unpairB2) (cpt_const [])
      (cpt_sel hm (cpt_const []) cpt_unpairB2)) (fun s => ?_)
    change sel (hd (unpairB s).2) [] (sel (bflag (memB
      (setLiteralSign true (headI (unpairB s).2)) (unpairB s).1)) [] (unpairB s).2) = _
    unfold keep
    cases h : (unpairB s).2 with
    | nil => rfl
    | cons a r =>
        cases a <;> cases b : memB (setLiteralSign true (headI (_ :: r))) (unpairB s).1 <;>
          simp [hd,sel,bflag,b]
  have h := cpt_comp cpt_pairB hb
  simpa [unpairB_pairB] using h

private theorem mem_reachable (φ : CNF) (x y : ℕ) :
    memB (encodeLiteral (y,true)) (closS (encodeCNF (variableGraph φ)) (encodeLiteral (x,true))) = true ↔
      connected φ x y := by
  have hwidth : ∀ c ∈ variableGraph φ, c.length = 1 ∨ c.length = 2 := fun c hc =>
    Or.inr (graph_binary φ c hc)
  rw [closS_enc _ hwidth,memB_encL,← graph_reach]
  exact ⟨clos_sound,clos_complete (rounds_le (variableGraph φ))⟩

/-- Extract, in canonical order, all clauses in the variable co-occurrence
component of the supplied literal, ignoring its sign. -/
theorem MeasuredCNFComponent :
    ∃ get : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) get ∧
      ∀ (l : Literal) (φ : CNF),
        get (encodeLiteral l,encodeCNF φ) = encodeCNF (φ.filter (fun c =>
          @decide (∃ m ∈ c, Relation.ReflTransGen (fun x y : ℕ =>
            ∃ d ∈ φ, x ∈ d.map Prod.fst ∧ y ∈ d.map Prod.fst) l.1 m.1) (Classical.propDecidable _))) := by
  classical
  obtain ⟨graph,hgraph,hgs⟩ := MeasuredVariableGraph
  obtain ⟨collect,hc,hcs⟩ := MeasuredClauseMap keep keep_cpt
  let close := fun s => closS (graph (unpairB s).2) (setLiteralSign true (unpairB s).1)
  let raw := fun s => collect (close s,(unpairB s).2)
  have hraw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_comp (cpt_pair (cpt_closS (cpt_comp cpt_unpairB2 hgraph)
      (setLiteralSign_cpt true cpt_unpairB1)) cpt_unpairB2) hc
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp (g := raw) cpt_pairB hraw,fun l φ => ?_⟩
  change raw (pairB (encodeLiteral l) (encodeCNF φ)) = encodeCNF (component φ l.1)
  simp only [raw,close,unpairB_pairB,hgs,setLiteralSign_spec,hcs]
  let closure := closS (encodeCNF (variableGraph φ)) (encodeLiteral (l.1,true))
  let P := fun c : Clause => ∃ m ∈ c, connected φ l.1 m.1
  have hkeep (c : Clause) (hc : c ∈ φ) :
      keep (closure,encodeClause c) = if P c then encodeClause c else [] := by
    cases c with
    | nil => simp [P,keep,encodeClause]
    | cons m c =>
        have hcode : encodeClause (m :: c) = encodeLiteral m ++ encodeClause c := by simp [encodeClause]
        have htag : (encodeLiteral m ++ encodeClause c).headD false = true := by simp [encodeLiteral_eq]
        have htest : memB (encodeLiteral (m.1,true)) closure = true ↔ P (m :: c) := by
          rw [mem_reachable]
          have h1 := component_first (x := l.1) m c hc
          rw [mem_component] at h1
          exact ⟨fun h => ⟨m,List.mem_cons_self,h⟩,fun h => h1.mp ⟨hc,h⟩⟩
        have hif : (if memB (encodeLiteral (m.1,true)) closure then encodeClause (m :: c) else []) =
            (if P (m :: c) then encodeClause (m :: c) else []) := by
          by_cases hP : P (m :: c)
          · simp [hP,htest.mpr hP]
          · simp [hP,show memB (encodeLiteral (m.1,true)) closure ≠ true from fun h => hP (htest.mp h)]
        simp only [keep,hcode,htag,ite_true,headI_lit,setLiteralSign_spec]
        simpa only [hcode] using hif
  have hscan (xs : CNF) :
      xs.flatMap (fun c => if P c then encodeClause c else []) = encodeCNF (xs.filter (fun c => @decide (P c) (Classical.propDecidable _))) := by
    induction xs with
    | nil => rfl
    | cons c xs ih =>
        by_cases h : P c <;> simp [h,ih,encodeCNF]
  apply Eq.trans (List.flatMap_congr hkeep)
  exact hscan φ

end PEqualNP.Outside
