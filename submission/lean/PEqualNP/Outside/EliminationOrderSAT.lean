import PEqualNP.Outside.MeasuredEliminationWalk
import PEqualNP.Outside.MeasuredVariableOrderCode
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.ProofComplexity (Satisfiable)

private abbrev Raw := List Bool

set_option maxHeartbeats 800000 in
/-- The language of canonical triples whose elimination stages lie in the
supplied universe and whose final stage has no clauses belongs to P. -/
theorem EliminationOrderSAT :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    {s : List Bool | ∃ φ U O : CNF,
      s = pair (encodeCNF O) (pair (encodeCNF φ) (encodeCNF U)) ∧
      let order := O.flatten.map Prod.fst
      (∀ j ≤ order.length, (order.take j).foldl eliminate (clauses φ) ⊆ clauses U) ∧
      order.foldl eliminate (clauses φ) = ∅} ∈ P := by
  dsimp only
  obtain ⟨run,hr,hrs⟩ := MeasuredEliminationWalk
  obtain ⟨normalize,hn,hns⟩ := MeasuredVariableOrderCode
  let getO := fun s : Raw => (unpairB s).1
  let getF := fun s : Raw => (unpairB (unpairB s).2).1
  let getU := fun s : Raw => (unpairB (unpairB s).2).2
  let rebuilt := fun s : Raw => pairB (getO s) (pairB (getF s) (getU s))
  let output := fun s : Raw => run (pairB (normalize (getO s)) (pairB (getF s) (getU s)))
  let flag := fun s : Raw =>
    sel (bflag (decide (rebuilt s = s))) []
      (sel (bflag (wfB (getO s))) []
        (sel (bflag (wfB (getF s))) []
          (sel (bflag (wfB (getU s))) [] (bflag (decide (output s = [true]))))))
  let accept := fun s : Raw => !(flag s).isEmpty
  have ho := cpt_unpairB1
  have hf := cpt_unpairB1_1 cpt_unpairB2
  have hu := cpt_unpairB2_1 cpt_unpairB2
  have hright := cpt_pairB2 hf hu
  have hpair := cpt_eqF (cpt_pairB2 ho hright) cpt_id
  have hoW := cpt_comp ho cpt_wfF
  have hfW := cpt_comp hf cpt_wfF
  have huW := cpt_comp hu cpt_wfF
  have hout := cpt_comp (cpt_pairB2 (cpt_comp ho hn) hright) hr
  have hlast := cpt_eqF hout (cpt_const [true])
  have hflag : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) flag :=
    cpt_sel hpair (cpt_const []) (cpt_sel hoW (cpt_const []) (cpt_sel hfW (cpt_const [])
      (cpt_sel huW (cpt_const []) hlast)))
  have haccept : ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool accept :=
    cpt_comp (g := fun s : Raw => !s.isEmpty) hflag bf_cpt_neL
  have hac (s : Raw) : accept s = true ↔ rebuilt s = s ∧ wfB (getO s) = true ∧
      wfB (getF s) = true ∧ wfB (getU s) = true ∧ output s = [true] := by
    unfold accept flag
    by_cases hp : rebuilt s = s <;> by_cases hlast : output s = [true] <;>
      cases wfB (getO s) <;> cases wfB (getF s) <;> cases wfB (getU s) <;>
      simp [hp,hlast,bflag,sel]
  have houtSpec (φ U O : CNF) :
      output (pairB (encodeCNF O) (pairB (encodeCNF φ) (encodeCNF U))) = [true] ↔
      (let order := O.flatten.map Prod.fst
       (∀ j ≤ order.length, (order.take j).foldl (fun G x => eliminateVariable x G) (clauseSet φ) ⊆ clauseSet U) ∧
       order.foldl (fun G x => eliminateVariable x G) (clauseSet φ) = ∅) := by
    let order := O.flatten.map Prod.fst
    have horder : ((O.flatten).map (fun l => (l.1,true))) = order.map (fun x => (x,true)) := by
      simp only [order,List.map_map,Function.comp_def]
    let result := run (pairB (encodeClause (order.map (fun x => (x,true))))
      (pairB (encodeCNF φ) (encodeCNF U)))
    have heq :
        output (pairB (encodeCNF O) (pairB (encodeCNF φ) (encodeCNF U))) = result := by
      simp only [output,getO,getF,getU,unpairB_pairB,hns,horder,result]
    rw [heq]
    let final := order.foldl (fun G x => eliminateVariable x G) (clauseSet φ)
    let covered := ∀ j ≤ order.length,
      (order.take j).foldl (fun G x => eliminateVariable x G) (clauseSet φ) ⊆ clauseSet U
    change result = [true] ↔ covered ∧ final = ∅
    have hs : (result ≠ [] ↔ covered) ∧ (result ≠ [] → ∃ ψ : CNF,
        result = true :: encodeCNF ψ ∧ clauseSet ψ = final) := hrs φ U order
    constructor
    · intro h
      have hnz : result ≠ [] := by rw [h]; decide
      obtain ⟨ψ,hψ,hset⟩ := hs.2 hnz
      rw [h] at hψ
      have hnil : encodeCNF ψ = [] := (List.cons.inj hψ).2.symm
      have hψ0 : ψ = [] := encodeCNF_injective (hnil.trans (show [] = encodeCNF [] by rfl))
      exact ⟨hs.1.mp hnz,hset.symm.trans ((clauseSet_eq_empty_iff ψ).mpr hψ0)⟩
    · rintro ⟨hcov,hfinal⟩
      obtain ⟨ψ,hψ,hset⟩ := hs.2 (hs.1.mpr hcov)
      have hz := (clauseSet_eq_empty_iff ψ).mp (hset.trans hfinal)
      rw [hψ,hz]
      rfl
  refine ⟨accept,fun s => (show accept s = true ↔ _ from ?_).symm,haccept⟩
  rw [hac]
  constructor
  · rintro ⟨hP,hO,hF,hU,hResult⟩
    obtain ⟨O,hO⟩ := (wfB_iff _).mp hO
    obtain ⟨φ,hF⟩ := (wfB_iff _).mp hF
    obtain ⟨U,hU⟩ := (wfB_iff _).mp hU
    have hs : s = pairB (encodeCNF O) (pairB (encodeCNF φ) (encodeCNF U)) := by
      unfold rebuilt at hP
      simpa only [hO,hF,hU] using hP.symm
    exact ⟨φ,U,O,hs,(houtSpec φ U O).mp (hs ▸ hResult)⟩
  · rintro ⟨φ,U,O,rfl,h⟩
    let s := pairB (encodeCNF O) (pairB (encodeCNF φ) (encodeCNF U))
    change rebuilt s = s ∧ wfB (getO s) = true ∧ wfB (getF s) = true ∧
      wfB (getU s) = true ∧ output s = [true]
    refine ⟨?_,?_,?_,?_,(houtSpec φ U O).mpr h⟩
    · simp [s,rebuilt,getO,getF,getU,unpairB_pairB]
    · simpa only [s,getO,unpairB_pairB] using (wfB_iff (encodeCNF O)).mpr ⟨O,rfl⟩
    · simpa only [s,getF,unpairB_pairB] using (wfB_iff (encodeCNF φ)).mpr ⟨φ,rfl⟩
    · simpa only [s,getU,unpairB_pairB] using (wfB_iff (encodeCNF U)).mpr ⟨U,rfl⟩

end PEqualNP.Outside
