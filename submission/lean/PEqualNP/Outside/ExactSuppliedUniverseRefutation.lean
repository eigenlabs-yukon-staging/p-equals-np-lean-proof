import PEqualNP.Outside.MeasuredUniverseResolution
import PEqualNP.Outside.ExactResolutionRefutationVerifier
import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

/-- Exact measured verification that a supplied finite canonical universe
contains a resolution refutation of the supplied canonical formula. -/
theorem ExactSuppliedUniverseRefutation :
    DecidableInPolyTime encodePair
      {p : List Bool × List Bool | ∃ φ U : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧
        ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
          ∀ d ∈ π, ∃ c ∈ U, c.toFinset = d} := by
  obtain ⟨derive,hd,hds⟩ := MeasuredUniverseResolution
  let R : Set (List Bool × List Bool) := {p | ∃ φ ρ : CNF, encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
    PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset)}
  have hR : DecidableInPolyTime encodePair R := ExactResolutionRefutationVerifier.1
  obtain ⟨verify,hv,hvc⟩ := hR
  let proofCheck := fun p : List Bool × List Bool => verify (p.1,derive p)
  let accept := fun p : List Bool × List Bool => wfB p.2 && proofCheck p
  have hc := cpt_comp (cpt_pairG cpt_fst hd) hvc
  have hr := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hc)
  have ht := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_comp cpt_pairB (cpt_sel (cpt_comp cpt_unpairB2 cpt_wfF) (cpt_const []) hr)) bf_cpt_neL
  have he :
      (fun p : List Bool × List Bool => !(sel (bflag (wfB p.2)) [] (if proofCheck p then [true] else [])).isEmpty) =
      accept := by
    funext p
    unfold accept
    cases wfB p.2 <;> cases proofCheck p <;> rfl
  simp only [unpairB_pairB] at ht
  rw [he] at ht
  refine ⟨accept,fun p => ?_,ht⟩
  have hsem (φ U : CNF) : proofCheck (encodeCNF φ,encodeCNF U) = true ↔
      ∃ π : List FinClause, PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) π ∧ ∀ d ∈ π, represented U d := by
    obtain ⟨ρ,hρ,hD,hU,hE⟩ := hds φ U
    have hEq : proofCheck (encodeCNF φ,encodeCNF U) = true ↔
        PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset) := by
      change verify (encodeCNF φ,derive (encodeCNF φ,encodeCNF U)) = true ↔ _
      rw [hρ,← hv]
      constructor
      · rintro ⟨f,r,hf,hr,h⟩
        have hf' := encodeCNF_injective hf
        have hr' := encodeCNF_injective hr
        subst f r
        exact h
      · exact fun h => ⟨φ,ρ,rfl,rfl,h⟩
    rw [hEq]
    constructor
    · exact fun h => ⟨_,h,hU⟩
    · intro h
      exact ⟨hD,(trace_empty_iff ρ).mp (hE.mpr h)⟩
  change (∃ φ U : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧
    ∃ π : List FinClause, PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) π ∧ ∀ d ∈ π, represented U d) ↔ accept p = true
  simp only [accept,Bool.and_eq_true]
  rcases p with ⟨x,u⟩
  constructor
  · rintro ⟨φ,U,rfl,rfl,h⟩
    exact ⟨(wfB_iff _).mpr ⟨U,rfl⟩,(hsem φ U).mpr h⟩
  · rintro ⟨hw,hh⟩
    obtain ⟨U,rfl⟩ := (wfB_iff _).mp hw
    have hR' : (x,derive (x,encodeCNF U)) ∈ R := (hv _).mpr hh
    obtain ⟨φ,ρ,hφ,_,_⟩ := hR'
    change encodeCNF φ = x at hφ
    subst x
    exact ⟨φ,U,rfl,rfl,(hsem φ U).mp hh⟩

end PEqualNP.Outside
