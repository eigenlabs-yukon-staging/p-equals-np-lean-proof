import PEqualNP.Outside.MeasuredMixedRadixUnits
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Library.L055

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

private def query (base extra : CNF) : List Bool := pairB (encodeCNF base) (encodeCNF extra)

private theorem encode_app (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF,List.flatMap_append]

private theorem eval_app (σ : Assignment) (a b : CNF) :
    CNF.eval σ (a ++ b) = true ↔ CNF.eval σ a = true ∧ CNF.eval σ b = true := by
  simp [CNF.eval,List.all_append]

/-- A supplied canonical base with a correct P solver on its width-one extensions
admits measured branching over an extra formula of polynomial width product. -/
theorem PackedProductBudgetSAT (B : Language Bool) (hB : B ∈ P) (q : Polynomial ℕ) :
    ∃ D : Language Bool, D ∈ P ∧ ∀ (base extra : CNF),
      (∀ units : CNF, IsKCNF 1 units → (encodeCNF (base ++ units) ∈ B ↔ Satisfiable (base ++ units))) →
      let raw := List.replicate (encodeCNF base).length true ++ false :: (encodeCNF base ++ encodeCNF extra)
      (extra.map List.length).prod ≤ q.eval raw.length →
        (raw ∈ D ↔ Satisfiable (base ++ extra)) := by
  obtain ⟨choose,hchoose,hsound,hcomplete⟩ := MeasuredMixedRadixUnits
  obtain ⟨accept,haccept,hc⟩ := hB
  let R : Set (List Bool × List Bool) := {p | p.2 ∈ B}
  have hR : DecidableInPolyTime encodePair R :=
    ⟨fun p => accept p.2,fun p => haccept p.2,cpt_comp cpt_snd hc⟩
  let clock := fun x : List Bool => List.replicate (q.eval x.length) true
  let gen := fun p : List Bool × List Bool =>
    (unpairB p.2).1 ++ choose (p.1,(unpairB p.2).2)
  have hgen : ComputableInPolyTime encodePair (fun x : List Bool => x) gen := by
    have hfirst := cpt_comp cpt_snd cpt_unpairB1
    have hsecond := cpt_comp cpt_snd cpt_unpairB2
    have hchoose' := cpt_comp (cpt_pairG cpt_fst hsecond) hchoose
    exact cpt_comp (cpt_pairG hfirst hchoose') cpt_append
  let D : Language Bool := {x | ∃ i < (clock x).length, (x,gen (List.replicate i true,x)) ∈ R}
  refine ⟨D,IndexedWitnessProjection R hR clock (L055 q) gen hgen,fun base extra hb => ?_⟩
  dsimp only
  change (extra.map List.length).prod ≤ q.eval (query base extra).length → _
  intro hbudget
  let x := query base extra
  change (∃ i < (clock x).length, gen (List.replicate i true,x) ∈ B) ↔ Satisfiable (base ++ extra)
  have hformula (i : ℕ) :
      gen (List.replicate i true,x) = encodeCNF base ++ choose (List.replicate i true,encodeCNF extra) := by
    simp only [gen,x,query,unpairB_pairB]
  constructor
  · rintro ⟨i,_,hi⟩
    obtain ⟨units,hunit,he,hs⟩ := hsound extra (List.replicate i true)
    rw [hformula,he,← encode_app] at hi
    obtain ⟨σ,hσ⟩ := (hb units hunit).mp hi
    obtain ⟨hbase,hU⟩ := (eval_app _ _ _).mp hσ
    exact ⟨σ,(eval_app _ _ _).mpr ⟨hbase,hs σ hU⟩⟩
  · rintro ⟨σ,hσ⟩
    obtain ⟨hbase,hE⟩ := (eval_app _ _ _).mp hσ
    obtain ⟨i,hidx,units,he,hU⟩ := hcomplete extra σ hE
    obtain ⟨units',hW,he',_⟩ := hsound extra (List.replicate i true)
    have e : units' = units := PEqualNP.Library.SearchHelpers.encodeCNF_injective (he'.symm.trans he)
    subst units'
    refine ⟨i,?_,?_⟩
    · simp only [clock,x,List.length_replicate]
      exact hidx.trans_le hbudget
    · rw [hformula,he,← encode_app]
      exact (hb units hW).mpr ⟨σ,(eval_app _ _ _).mpr ⟨hbase,hU⟩⟩

end PEqualNP.Outside
