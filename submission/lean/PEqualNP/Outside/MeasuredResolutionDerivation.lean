import PEqualNP.Outside.MeasuredResolutionLine
import PEqualNP.Outside.MeasuredClauseSuffixChecks
import PEqualNP.Outside.UnitPropagationCorrect

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private def valid (φ ρ : CNF) (c : Clause) : Prop :=
  (∃ a ∈ φ, a.toFinset = c.toFinset) ∨
  ∃ a ∈ ρ, ∃ b ∈ ρ, PEqualNP.ProofComplexity.IsResolvent a.toFinset b.toFinset c.toFinset

private theorem exact_suffix (φ ρ : CNF) :
    suffixChecks valid φ ρ ↔ PEqualNP.ProofComplexity.IsDerivation (clauseSet φ) (ρ.map List.toFinset) := by
  induction ρ with
  | nil =>
      constructor
      · intro _
        exact .nil
      · intro _ pre c older he
        cases pre <;> simp at he
  | cons c ρ ih =>
      rw [suffixChecks_cons,ih,List.map_cons]
      constructor
      · rintro ⟨h,hD⟩
        rcases h with h | ⟨a,ha,b,hb,hr⟩
        · exact .ax hD h
        · exact .res hD (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hr
      · intro h
        cases h with
        | ax hD hA => exact ⟨Or.inl hA,hD⟩
        | res hD hA hB hR =>
            obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hA
            obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hB
            exact ⟨Or.inr ⟨a,ha,b,hb,hR⟩,hD⟩

/-- Check every decoded line of a newest-first resolution derivation.
A parent can only be used from the exact older suffix. -/
theorem MeasuredResolutionDerivation :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ ρ : CNF), test (encodeCNF φ,encodeCNF ρ) = true ↔
        PEqualNP.ProofComplexity.IsDerivation
          {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) := by
  obtain ⟨line,hl,hs⟩ := MeasuredResolutionLine
  obtain ⟨test,ht,hts⟩ := MeasuredClauseSuffixChecks valid line hl hs
  exact ⟨test,ht,fun φ ρ => (hts φ ρ).trans (exact_suffix φ ρ)⟩

end PEqualNP.Outside
