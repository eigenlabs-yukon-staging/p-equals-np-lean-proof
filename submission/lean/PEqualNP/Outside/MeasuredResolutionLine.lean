import PEqualNP.Outside.MeasuredResolutionStep
import PEqualNP.Outside.MeasuredClauseMap

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private abbrev Raw := List Bool

private def parentFlags (step : Raw → Bool) (p : Raw × Raw) : Raw :=
  bflag (step (pairB (unpairB p.1).1 (pairB p.2 (unpairB p.1).2)))

private theorem parentFlags_cpt {step : Raw → Bool}
    (hs : ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool step) :
    ComputableInPolyTime encodePair (fun x : Raw => x) (parentFlags step) := by
  have ht := cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB1)
    (cpt_pairB2 cpt_unpairB2 (cpt_unpairB2_1 cpt_unpairB1))
  have hh := cpt_comp cpt_pairB (cpt_bitFlag (cpt_comp ht hs))
  change ComputableInPolyTime _ _ (fun p : Raw × Raw =>
    bflag (step (pairB (unpairB p.1).1 (pairB p.2 (unpairB p.1).2))))
  simpa only [unpairB_pairB,bflag] using hh

/-- A measured local Boolean verifier for one line of a resolution trace. -/
theorem MeasuredResolutionLine :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    ∃ test : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test ∧
      ∀ (φ ρ : CNF) (c : Clause),
        test (pair (encodeCNF φ) (pair (encodeCNF ρ) (encodeClause c))) = true ↔
          (∃ a ∈ φ, a.toFinset = c.toFinset) ∨
          ∃ a ∈ ρ, ∃ b ∈ ρ, PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset := by
  classical
  obtain ⟨eq,he,hess⟩ := MeasuredClauseSetEquality
  obtain ⟨step,hs,hstep⟩ := MeasuredResolutionStep
  let ax := fun p : Raw × Raw => if eq (p.2,p.1) then [true] else []
  have ha : ComputableInPolyTime encodePair (fun x : Raw => x) ax :=
    cpt_bitFlag (cpt_comp (cpt_pairG cpt_snd cpt_fst) he)
  obtain ⟨axes,haxes,haxs⟩ := MeasuredClauseMap ax ha
  obtain ⟨parents,hparents,hpS⟩ := MeasuredClauseMap _ (parentFlags_cpt hs)
  let outer := fun p : Raw × Raw => parents (pairB p.2 (unpairB p.1).2,(unpairB p.1).1)
  have houter : ComputableInPolyTime encodePair (fun x : Raw => x) outer := by
    have hh := cpt_comp (cpt_pair (cpt_pairB2 cpt_unpairB2 (cpt_unpairB2_1 cpt_unpairB1))
      (cpt_unpairB1_1 cpt_unpairB1)) hparents
    simpa only [outer,unpairB_pairB] using cpt_comp cpt_pairB hh
  obtain ⟨res,hres,hrS⟩ := MeasuredClauseMap outer houter
  let all := fun s => axes ((unpairB (unpairB s).2).2,(unpairB s).1) ++
    res ((unpairB s).2,(unpairB (unpairB s).2).1)
  have hx := cpt_comp (cpt_pair (cpt_unpairB2_1 cpt_unpairB2) cpt_unpairB1) haxes
  have hy := cpt_comp (cpt_pair cpt_unpairB2 (cpt_unpairB1_1 cpt_unpairB2)) hres
  refine ⟨fun s => !(all s).isEmpty,
    cpt_comp (g := fun w : Raw => !w.isEmpty) (cpt_app2 hx hy) bf_cpt_neL,fun φ ρ c => ?_⟩
  change (!(all (pairB (encodeCNF φ) (pairB (encodeCNF ρ) (encodeClause c)))).isEmpty) = true ↔ _
  have hax (a : Clause) : ax (encodeClause c,encodeClause a) ≠ [] ↔ a.toFinset = c.toFinset := by
    rw [← hess]
    unfold ax
    cases eq (encodeClause a,encodeClause c) <;> decide
  have hrow (a b : Clause) :
      parentFlags step (pairB (encodeClause a) (encodeClause c),encodeClause b) ≠ [] ↔
      PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset := by
    simp only [parentFlags,unpairB_pairB]
    have hstep' : step (pairB (encodeClause a) (pairB (encodeClause b) (encodeClause c))) = true ↔
        PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset := hstep a b c
    rw [← hstep']
    cases step (pairB (encodeClause a) (pairB (encodeClause b) (encodeClause c))) <;> decide
  simp only [all,unpairB_pairB,haxs,hrS,outer,hpS,Bool.not_eq_true',List.isEmpty_eq_false_iff,ne_eq,
    List.append_eq_nil_iff,List.flatMap_eq_nil_iff,not_and_or]
  push Not
  exact or_congr
    (exists_congr (fun a => and_congr_right (fun _ => hax a)))
    (exists_congr (fun a => and_congr_right (fun _ =>
      exists_congr (fun b => and_congr_right (fun _ => hrow a b)))))

end PEqualNP.Outside
