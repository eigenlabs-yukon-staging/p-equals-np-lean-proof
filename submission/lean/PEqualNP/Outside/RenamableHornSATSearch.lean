import PEqualNP.Outside.RestrictionClosedSATSearch
import PEqualNP.Outside.RenamableHornSATInP

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.PartialAssignmentFacts (retained_clause)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

theorem PEqualNP.Outside.RenamableHornSATSearch :
    ∃ find : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) find ∧
      ∀ φ : CNF, (∃ ρ : Assignment, ∀ c ∈ φ,
        (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1) →
        Satisfiable φ →
        ∃ v : List ℕ,
          find (encodeCNF φ) = encodeCNF (v.map (fun i => [(i, true)])) ∧
          CNF.eval (fun i => decide (i ∈ v)) φ = true := by
  let F : Set CNF := {φ | ∃ ρ : Assignment, ∀ c ∈ φ,
    (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1}
  let L : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧ φ ∈ F}
  have hP : L ∈ P := RenamableHornSATInP
  have hclosed (ρ : ℕ → Option Bool) (φ : CNF) (hφ : φ ∈ F) : restrict ρ φ ∈ F := by
    obtain ⟨flip, hflip⟩ := hφ
    refine ⟨flip, ?_⟩
    intro c hc
    obtain ⟨d, hd, he⟩ := retained_clause hc
    have hsub : c.Sublist d := by
      rw [he]
      exact List.filter_sublist
    exact (hsub.filter (fun l => xor l.2 (flip l.1))).length_le.trans (hflip d hd)
  have hcorrect (φ : CNF) (hφ : φ ∈ F) : encodeCNF φ ∈ L ↔ Satisfiable φ := by
    constructor
    · rintro ⟨ψ, he, hs, _⟩
      rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
    · exact fun h => ⟨φ, rfl, h, hφ⟩
  exact RestrictionClosedSATSearch F L hP hclosed hcorrect
