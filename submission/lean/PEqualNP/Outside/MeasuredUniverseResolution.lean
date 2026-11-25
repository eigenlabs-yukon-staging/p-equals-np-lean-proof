import PEqualNP.Outside.MeasuredResolutionSaturation
import PEqualNP.Outside.ResolutionWithinUniverse

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Search

/-- For a supplied finite universe of canonical clauses, construct an
exact derivation and detect all refutations represented within that universe. -/
theorem MeasuredUniverseResolution :
    ∃ derive : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) derive ∧
      ∀ φ U : CNF, ∃ ρ : CNF, derive (encodeCNF φ,encodeCNF U) = encodeCNF ρ ∧
        PEqualNP.ProofComplexity.IsDerivation
          {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) ∧
        (∀ d ∈ ρ.map List.toFinset, ∃ c ∈ U, c.toFinset = d) ∧
        ([] ∈ ρ ↔ ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
          ∀ d ∈ π, ∃ c ∈ U, c.toFinset = d) := by
  obtain ⟨derive,hd,hds⟩ := measuredResolutionSaturationOnPair
  refine ⟨derive,hd,fun φ U => ?_⟩
  let n := (encodeCNF U).length
  let ρ := resolutionTrace φ U n
  refine ⟨ρ,hds φ U,resolutionTrace_derives φ U n,?_,trace_within_universe φ U n ?_⟩
  · intro d hd
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    exact ⟨c,resolutionTrace_subset φ U n hc,rfl⟩
  · induction U with
    | nil => rfl
    | cons c U ih =>
        have h : encodeCNF (c :: U) = encodeClause c ++ encodeCNF U := by simp [encodeCNF]
        change U.length ≤ (encodeCNF U).length at ih
        change (c :: U).length ≤ (encodeCNF (c :: U)).length
        rw [List.length_cons,h,List.length_append]
        have hlen : 1 ≤ (encodeClause c).length := by simp [encodeClause]
        omega

end PEqualNP.Outside
