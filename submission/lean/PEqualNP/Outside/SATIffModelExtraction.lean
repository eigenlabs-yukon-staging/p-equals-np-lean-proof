import PEqualNP.Outside.RestrictionSearchSemantics
import PEqualNP.Library.SearchHelpers.SatVerifierCPT

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.RestrictionSearchSemantics (solve hereditary)
open PEqualNP.Outside.TwoSatGreedyCore (finish finish_cpt)
open PEqualNP.Outside.CnfRestrictionSemantics (names)
open PEqualNP.Outside.HornRenameMachine (flips)

private theorem sat_enc (φ : CNF) : encodeCNF φ ∈ SAT ↔ Satisfiable φ := by
  constructor
  · rintro ⟨ψ, he, hs⟩
    rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
  · exact fun h => ⟨φ, rfl, h⟩

theorem PEqualNP.Outside.SATIffModelExtraction :
    SAT ∈ P ↔
      ∃ find : List Bool → List Bool,
        ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) find ∧
        ∀ φ : CNF, Satisfiable φ →
          ∃ v : List ℕ,
            find (encodeCNF φ) = v.flatMap (fun i => (encodeLiteral (i, true)).drop 2) ∧
            CNF.eval (fun i => decide (i ∈ v)) φ = true := by
  constructor
  · rintro ⟨dec, hd, hc⟩
    let find (x : List Bool) := finish dec (x, x)
    refine ⟨find, cpt_comp (cpt_pair cpt_id cpt_id) (finish_cpt hc), ?_⟩
    intro φ hs
    let F : Set CNF := Set.univ
    have hclosed : hereditary F := by simp [hereditary, F]
    have hcorrect : ∀ ψ ∈ F, Satisfiable ψ ↔ dec (encodeCNF ψ) = true :=
      fun ψ _ => (sat_enc ψ).symm.trans (hd _)
    obtain ⟨v, hcode, hv⟩ := solve F hclosed dec hcorrect φ φ (by simp [F]) hs
      (fun c hc l hl => ⟨c, hc, l, hl, rfl⟩)
    refine ⟨v, ?_, hv⟩
    unfold find
    rw [hcode]
    simp [names, encodeLiteral_eq]
  · rintro ⟨find, htime, hfind⟩
    let dec (x : List Bool) := SV (x, find x)
    refine ⟨dec, ?_, cpt_comp (cpt_pair cpt_id htime) cpt_SV⟩
    intro x
    constructor
    · rintro ⟨φ, rfl, hs⟩
      obtain ⟨v, hcode, hv⟩ := hfind φ hs
      have he : find (encodeCNF φ) = v.flatMap vcode := by
        simpa [encodeLiteral_eq] using hcode
      have hag : asg (find (encodeCNF φ)) = flips v := by
        rw [he]
        funext i
        by_cases h : i ∈ v
        · have ht := (asg_codes v i).mpr h
          rw [ht]
          simp [flips, h]
        · cases h' : asg (v.flatMap vcode) i
          · simp [flips, h]
          · exact False.elim (h ((asg_codes v i).mp h'))
      have hw : wfB (encodeCNF φ) = true := (wfB_iff _).mpr ⟨φ, rfl⟩
      unfold dec SV
      simpa [hw, evalB_enc, hag] using (show CNF.eval (flips v) φ = true from hv)
    · intro h
      obtain ⟨φ, he, hs⟩ := (SV_iff x (find x)).mp h
      exact ⟨φ, he, asg (find x), hs⟩
