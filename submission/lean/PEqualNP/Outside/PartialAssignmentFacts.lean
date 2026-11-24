import PEqualNP.Outside.CnfRestrictionSemantics

namespace PEqualNP.Outside.PartialAssignmentFacts

open PEqualNP.Search
open PEqualNP.Outside.RestrictCnfHelpers
open PEqualNP.Outside.CnfRestrictionSemantics (valueOf)

def assignment (a : Finset ℕ) (σ : Assignment) (i : ℕ) : Option Bool :=
  if i ∈ a then some (σ i) else none

theorem valueOf_filter (k : List ℕ) (σ : Assignment) :
    valueOf k (k.filter σ) = assignment k.toFinset σ := by
  funext i
  by_cases hi : i ∈ k
  · cases h : σ i <;> simp [valueOf, assignment, hi, h, List.mem_filter]
  · simp [valueOf, assignment, hi]

theorem retained_clause {φ : CNF} {ρ : ℕ → Option Bool} {c : Clause}
    (hc : c ∈ restrict ρ φ) :
    ∃ c₀ ∈ φ, c = c₀.filter (fun l => (ρ l.1).isNone) := by
  obtain ⟨c₀, hmem, h⟩ := List.mem_filterMap.mp hc
  by_cases hs : c₀.any (fun l => ρ l.1 == some l.2) = true
  · simp [hs] at h
  · refine ⟨c₀, hmem, ?_⟩
    simpa [hs, eq_comm] using h


end PEqualNP.Outside.PartialAssignmentFacts
