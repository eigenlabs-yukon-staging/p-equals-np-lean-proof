import PEqualNP.Outside.DavisPutnamElimination
import PEqualNP.Outside.MeasuredPivotClauseFilter
import PEqualNP.Outside.MeasuredClauseSetEquality
import PEqualNP.Outside.UnitPropagationCorrect

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

private def neutral (x : ℕ) (φ : CNF) :=
  φ.filter (fun c => decide ((x,true) ∉ c ∧ (x,false) ∉ c))
private def positive (x : ℕ) (φ : CNF) :=
  φ.filter (fun c => decide ((x,true) ∈ c ∧ (x,false) ∉ c))
private def negative (x : ℕ) (φ : CNF) :=
  φ.filter (fun c => decide ((x,true) ∉ c ∧ (x,false) ∈ c))

private def eraseLit (l : Literal) (c : Clause) := c.filter (fun m => decide (m ≠ l))
private def resolveAt (x : ℕ) (p n : Clause) := eraseLit (x,true) p ++ eraseLit (x,false) n
private def updated (x : ℕ) (φ : CNF) : CNF :=
  neutral x φ ++ (positive x φ).flatMap (fun p => (negative x φ).map (resolveAt x p))

private theorem erase_set (l : Literal) (c : Clause) : (eraseLit l c).toFinset = c.toFinset.erase l := by
  ext m
  simp only [eraseLit,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_erase]
  exact and_comm

private theorem resolve_set (x : ℕ) (p n : Clause) :
    (resolveAt x p n).toFinset = p.toFinset.erase (x,true) ∪ n.toFinset.erase (x,false) := by
  simp only [resolveAt,List.toFinset_append,erase_set]

private theorem updated_set (x : ℕ) (φ : CNF) : clauseSet (updated x φ) = eliminateVariable x (clauseSet φ) := by
  ext d
  constructor
  · rintro ⟨c,hc,rfl⟩
    rw [updated,List.mem_append] at hc
    rcases hc with h | h
    · obtain ⟨hc,hpred⟩ := List.mem_filter.mp h
      obtain ⟨hp,hn⟩ := of_decide_eq_true hpred
      exact Or.inl ⟨⟨c,hc,rfl⟩,fun h => hp (List.mem_toFinset.mp h),fun h => hn (List.mem_toFinset.mp h)⟩
    · simp only [List.mem_flatMap,List.mem_map] at h
      obtain ⟨p,hp,n,hn,rfl⟩ := h
      obtain ⟨hp,hpred⟩ := List.mem_filter.mp hp
      obtain ⟨hpp,hpn⟩ := of_decide_eq_true hpred
      obtain ⟨hn,hpred⟩ := List.mem_filter.mp hn
      obtain ⟨hnp,hnn⟩ := of_decide_eq_true hpred
      exact Or.inr ⟨p.toFinset,⟨p,hp,rfl⟩,n.toFinset,⟨n,hn,rfl⟩,List.mem_toFinset.mpr hpp,
        fun h => hpn (List.mem_toFinset.mp h),List.mem_toFinset.mpr hnn,fun h => hnp (List.mem_toFinset.mp h),
        resolve_set x p n⟩
  · rintro (⟨⟨c,hc,rfl⟩,hp,hn⟩ | ⟨P,⟨p,hp,rfl⟩,N,⟨n,hn,rfl⟩,hpp,hpn,hnn,hnp,rfl⟩)
    · refine ⟨c,List.mem_append_left _ (List.mem_filter.mpr ⟨hc,?_⟩),rfl⟩
      exact decide_eq_true ⟨fun h => hp (List.mem_toFinset.mpr h),fun h => hn (List.mem_toFinset.mpr h)⟩
    · refine ⟨resolveAt x p n,List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,?_,List.mem_map.mpr ⟨n,?_,rfl⟩⟩),
        resolve_set x p n⟩
      · exact List.mem_filter.mpr ⟨hp,decide_eq_true ⟨List.mem_toFinset.mp hpp,fun h => hpn (List.mem_toFinset.mpr h)⟩⟩
      · exact List.mem_filter.mpr ⟨hn,decide_eq_true ⟨fun h => hnp (List.mem_toFinset.mpr h),List.mem_toFinset.mp hnn⟩⟩

private def payload (erase : Raw × Raw → Raw) (p : Raw × Raw) : Raw :=
  erase ((unpairB p.1).1,(unpairB p.1).2) ++ erase (negI (unpairB p.1).1,p.2) ++ [false,false]

private theorem payload_cpt {erase : Raw × Raw → Raw}
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase) :
    ComputableInPolyTime encodePair (fun x : Raw => x) (payload erase) := by
  have hI := cpt_unpairB1_1 cpt_unpairB1
  have hA := cpt_unpairB2_1 cpt_unpairB1
  have hB := cpt_unpairB2
  have hp := cpt_comp (cpt_pair hI hA) he
  have hn := cpt_comp (cpt_pair (cpt_negI hI) hB) he
  have h : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => payload erase (unpairB s)) :=
    cpt_app2 (cpt_app2 hp hn) (cpt_const [false,false])
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

/-- One Davis–Putnam elimination step is a measured transformation of
the paired positive pivot code and canonical CNF. -/
theorem MeasuredDavisPutnamStep :
    ∃ eliminate : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) eliminate ∧
      ∀ (x : ℕ) (φ : CNF), ∃ ψ : CNF, eliminate (encodeLiteral (x,true),encodeCNF φ) = encodeCNF ψ ∧
        {c : PEqualNP.ProofComplexity.Clause ℕ | ∃ d ∈ ψ, d.toFinset = c} =
        {C : PEqualNP.ProofComplexity.Clause ℕ |
          ((∃ c ∈ φ, c.toFinset = C) ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
          ∃ P, (∃ c ∈ φ, c.toFinset = P) ∧ ∃ N, (∃ c ∈ φ, c.toFinset = N) ∧
            (x,true) ∈ P ∧ (x,false) ∉ P ∧ (x,false) ∈ N ∧ (x,true) ∉ N ∧
            C = P.erase (x,true) ∪ N.erase (x,false)} := by
  obtain ⟨keep,hkeep,hks⟩ := MeasuredPivotClauseFilter false false
  obtain ⟨pos,hpos,hps⟩ := MeasuredPivotClauseFilter true false
  obtain ⟨negatives,hneg,hns⟩ := MeasuredPivotClauseFilter false true
  obtain ⟨erase,he,hes⟩ := measuredLiteralPayloadErase
  obtain ⟨rows,hrows,hrs⟩ := MeasuredClauseMap (payload erase) (payload_cpt he)
  let mapPos := fun p : Raw × Raw => rows (pairB (unpairB p.1).1 p.2,(unpairB p.1).2)
  have hm : ComputableInPolyTime encodePair (fun x : Raw => x) mapPos := by
    have h := cpt_comp (cpt_pair (cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB1) cpt_unpairB2)
      (cpt_unpairB2_1 cpt_unpairB1)) hrows
    simpa only [unpairB_pairB,mapPos] using cpt_comp cpt_pairB h
  obtain ⟨all,hall,has⟩ := MeasuredClauseMap mapPos hm
  let raw := fun s => keep (unpairB s) ++ all (pairB (unpairB s).1 (negatives (unpairB s)),pos (unpairB s))
  have join := cpt_pair cpt_unpairB1 cpt_unpairB2
  have hraw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) raw :=
    cpt_app2 (cpt_comp join hkeep)
      (cpt_comp (cpt_pair (cpt_pairB2 cpt_unpairB1 (cpt_comp join hneg)) (cpt_comp join hpos)) hall)
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp (g := raw) cpt_pairB hraw,fun x φ => ⟨updated x φ,?_,updated_set x φ⟩⟩
  have hk : keep (encodeLiteral (x,true),encodeCNF φ) = encodeCNF (neutral x φ) := by
    simpa [neutral,decide_eq_false_iff_not] using hks x φ
  have hp : pos (encodeLiteral (x,true),encodeCNF φ) = encodeCNF (positive x φ) := by
    simpa [positive,decide_eq_false_iff_not] using hps x φ
  have hn : negatives (encodeLiteral (x,true),encodeCNF φ) = encodeCNF (negative x φ) := by
    simpa [negative,decide_eq_false_iff_not] using hns x φ
  change raw (pairB (encodeLiteral (x,true)) (encodeCNF φ)) = _
  simp only [raw,unpairB_pairB,hk,hp,hn,has,mapPos,hrs,payload,negI_lit,show neg (x,true) = (x,false) by rfl,hes]
  have h (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by simp [encodeCNF]
  rw [updated,h]
  apply congrArg (fun z => encodeCNF (neutral x φ) ++ z)
  simp only [encodeCNF,List.flatMap_assoc,List.flatMap_map,Function.comp_apply,resolveAt,eraseLit,encodeClause,List.flatMap_append]

end PEqualNP.Outside
