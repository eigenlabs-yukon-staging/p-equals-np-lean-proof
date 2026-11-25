import PEqualNP.Outside.ExactSuppliedUniverseRefutation
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Search

/-- Return a canonical resolution refutation from a supplied clause
universe, or the empty word when there is no represented refutation. -/
theorem SuppliedUniverseRefutationSearch :
    let covered := fun p : List Bool × List Bool => ∃ φ U : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧
      ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
        PEqualNP.ProofComplexity.IsRefutation
          {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
        ∀ d ∈ π, ∃ c ∈ U, c.toFinset = d
    ∃ search : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) search ∧
      ∀ p : List Bool × List Bool, (search p ≠ [] ↔ covered p) ∧
        (search p ≠ [] → ∃ φ U ρ : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧ encodeCNF ρ = search p ∧
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) ∧
          ∀ d ∈ ρ.map List.toFinset, ∃ c ∈ U, c.toFinset = d) := by
  let R : Set (List Bool × List Bool) := {p | ∃ φ U : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧
    ∃ π : List FinClause, PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) π ∧ ∀ d ∈ π, represented U d}
  have hR : DecidableInPolyTime encodePair R := ExactSuppliedUniverseRefutation
  obtain ⟨test,ht,hct⟩ := hR
  obtain ⟨derive,hd,hds⟩ := MeasuredUniverseResolution
  let search := fun p : List Bool × List Bool => sel (if test p then [true] else []) [] (derive p)
  have hraw := cpt_sel (cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hct))
    (cpt_const []) (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hd)
  have hs : ComputableInPolyTime encodePair (fun x : List Bool => x) search := by
    simpa only [unpairB_pairB,search] using cpt_comp cpt_pairB hraw
  refine ⟨search,hs,fun p => ?_⟩
  have hcert : p ∈ R → ∃ φ U ρ : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧ encodeCNF ρ = search p ∧
      PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset) ∧
      ∀ d ∈ ρ.map List.toFinset, represented U d := by
    intro h
    have htest := (ht p).mp h
    rcases p with ⟨a,b⟩
    obtain ⟨φ,U,rfl,rfl,h⟩ := h
    obtain ⟨ρ,hρ,hDer,hU,hEmpty⟩ := hds φ U
    have h : (∅ : FinClause) ∈ ρ.map List.toFinset := (trace_empty_iff ρ).mp (hEmpty.mpr h)
    exact ⟨φ,U,ρ,rfl,rfl,by simp [search,sel,htest,hρ],⟨hDer,h⟩,hU⟩
  have hiff : search p ≠ [] ↔ p ∈ R := by
    constructor
    · intro h
      apply (ht p).mpr
      cases he : test p with
      | false => exact (h (by simp [search,sel,he])).elim
      | true => rfl
    · intro h
      obtain ⟨φ,U,ρ,_,_,hρ,hR,_⟩ := hcert h
      intro hzero
      have hn := encodeCNF_injective (hρ.trans (hzero.trans (show [] = encodeCNF [] by rfl)))
      subst ρ
      exact List.not_mem_nil hR.2
  exact ⟨hiff,fun h => hcert (hiff.mp h)⟩

end PEqualNP.Outside
