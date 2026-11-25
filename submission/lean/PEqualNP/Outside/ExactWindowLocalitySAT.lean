import PEqualNP.Outside.MeasuredLocalityClauseUniverse
import PEqualNP.Outside.LocalityUniverseCoverage
import PEqualNP.Outside.MeasuredFirstOccurrenceLocality
import PEqualNP.Outside.MeasuredEliminationWalk
import PEqualNP.Outside.FullEliminationSAT
import PEqualNP.Outside.MeasuredVariableOrderCode
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Library.SearchHelpers.TwoSat

private abbrev Raw := List Bool

private theorem cnf_sat (φ : CNF) :
    PEqualNP.ProofComplexity.Satisfiable (clauseSet φ) ↔ Satisfiable φ := by
  have he (a : Assignment) : CNF.eval a φ = true ↔ PEqualNP.ProofComplexity.Satisfies a (clauseSet φ) := by
    simp only [CNF.eval,List.all_eq_true,Clause.eval,List.any_eq_true,Literal.eval,beq_iff_eq]
    constructor
    · rintro h C ⟨c,hc,rfl⟩
      obtain ⟨l,hl,ha⟩ := h c hc
      exact ⟨l,List.mem_toFinset.mpr hl,ha⟩
    · intro h c hc
      obtain ⟨l,hl,ha⟩ := h c.toFinset ⟨c,hc,rfl⟩
      exact ⟨l,List.mem_toFinset.mp hl,ha⟩
  exact exists_congr (fun a => (he a).symm)

private theorem marker_iff (w : Raw) (F : Set NatClause)
    (h : ∃ ψ : CNF, w = true :: encodeCNF ψ ∧ clauseSet ψ = F) : w = [true] ↔ F = ∅ := by
  obtain ⟨ψ,hψ,hF⟩ := h
  rw [hψ,← hF,clauseSet_eq_empty_iff]
  constructor
  · intro he
    exact encodeCNF_injective ((List.cons.inj he).2.trans (show [] = encodeCNF [] by rfl))
  · rintro rfl
    rfl

/-- Check exact first-occurrence locality and decide satisfiability using
only the measured linear-row window catalogue for the elimination walk. -/
theorem ExactWindowLocalitySAT (k : ℕ) :
    {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧ Satisfiable φ ∧
      let order := φ.flatten.map Prod.fst
      ∀ c ∈ φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k} ∈ P := by
  obtain ⟨gen,hg,hgs⟩ := MeasuredLocalityClauseUniverse k
  obtain ⟨norm,hn,hns⟩ := MeasuredVariableOrderCode
  obtain ⟨guard,hd,hds⟩ := MeasuredFirstOccurrenceLocality k
  obtain ⟨walk,hw,hws⟩ := MeasuredEliminationWalk
  let run := fun s : Raw => walk (pairB (norm s) (pairB s (gen (norm s))))
  have hr : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) run :=
    cpt_comp (cpt_pairB2 hn (cpt_pairB2 cpt_id (cpt_comp hn hg))) hw
  let flag := fun s : Raw =>
    sel (bflag (wfB s)) [] (sel (bflag (guard s)) [] (bflag (decide (run s = [true]))))
  let accept := fun s : Raw => !(flag s).isEmpty
  have hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) flag :=
    cpt_sel cpt_wfF (cpt_const []) (cpt_sel (cpt_bitFlag hd) (cpt_const []) (cpt_eqF hr (cpt_const [true])))
  have ha : ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool accept :=
    cpt_comp (g := fun s : Raw => !s.isEmpty) hf bf_cpt_neL
  have hAccept (s : Raw) : accept s = true ↔ wfB s = true ∧ guard s = true ∧ run s = [true] := by
    unfold accept flag
    by_cases h : run s = [true] <;> cases wfB s <;> cases guard s <;> simp [bflag,sel,h]
  have hRun (φ : CNF) (hLoc : guard (encodeCNF φ) = true) :
      run (encodeCNF φ) = [true] ↔ Satisfiable φ := by
    let c := φ.flatten.map (fun l => (l.1,true))
    let order := φ.flatten.map Prod.fst
    have hNorm : norm (encodeCNF φ) = encodeClause c := hns φ
    have hOrder : c.map Prod.fst = order := by simp [c,order,List.map_map,Function.comp_def]
    have hCode : c = order.map (fun x => (x,true)) := by simp [c,order,List.map_map,Function.comp_def]
    obtain ⟨U,hU,_,hRep⟩ := hgs c
    have hLoc' : ∀ d ∈ clauseSet φ, ∀ l ∈ d, ∀ m ∈ d, order.idxOf l.1 ≤ order.idxOf m.1 + k := by
      rintro d ⟨e,he,rfl⟩ l hl m hm
      exact (hds φ).mp hLoc e he l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm)
    have hSupp : ∀ d ∈ clauseSet φ, ∀ l ∈ d, l.1 ∈ order := by
      rintro d ⟨e,he,rfl⟩ l hl
      exact List.mem_map.mpr ⟨l,List.mem_flatten.mpr ⟨e,he,List.mem_toFinset.mp hl⟩,rfl⟩
    have hCov := LocalityUniverseCoverage k (clauseSet φ) c U hRep
    rw [hOrder] at hCov
    have hCover := hCov hLoc' hSupp
    let w := walk (pairB (encodeClause (order.map (fun x => (x,true)))) (pairB (encodeCNF φ) (encodeCNF U)))
    let final := order.foldl (fun G x => eliminateVariable x G) (clauseSet φ)
    have hResult : (w ≠ [] → ∃ ψ : CNF, w = true :: encodeCNF ψ ∧ clauseSet ψ = final) := (hws φ U order).2
    have hNZ : w ≠ [] := (hws φ U order).1.mpr hCover
    have hSat : PEqualNP.ProofComplexity.Satisfiable (clauseSet φ) ↔ final = ∅ :=
      FullEliminationSAT (clauseSet φ) order hSupp
    have hWord : run (encodeCNF φ) = w := by
      simp only [run,w,hNorm,hU]
      rw [hCode]
    rw [hWord]
    exact (marker_iff w final (hResult hNZ)).trans (hSat.symm.trans (cnf_sat φ))
  refine ⟨accept,fun s => (show accept s = true ↔ _ from ?_).symm,ha⟩
  rw [hAccept]
  constructor
  · rintro ⟨hSyntax,hLoc,hResult⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff s).mp hSyntax
    exact ⟨φ,rfl,(hRun φ hLoc).mp hResult,(hds φ).mp hLoc⟩
  · rintro ⟨φ,rfl,hSat,hLoc⟩
    have hg := (hds φ).mpr hLoc
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,hg,(hRun φ hg).mpr hSat⟩

end PEqualNP.Outside
