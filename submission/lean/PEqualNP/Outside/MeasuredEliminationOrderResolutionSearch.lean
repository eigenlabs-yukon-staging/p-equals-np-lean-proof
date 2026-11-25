import PEqualNP.Outside.EliminationOrderRefutation
import PEqualNP.Outside.SuppliedUniverseRefutationSearch

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.SearchHelpers
open PEqualNP.Search

/-- A supplied universe containing all stages of a covering elimination
order supports an exact measured resolution search for the input formula. -/
theorem MeasuredEliminationOrderResolutionSearch :
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ∃ search : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) search ∧
      ∀ (φ U : CNF) (order : List ℕ),
        (∀ c ∈ clauses φ, ∀ l ∈ c, l.1 ∈ order) →
        (∀ i ≤ order.length, (order.take i).foldl eliminate (clauses φ) ⊆ clauses U) →
        let result := search (encodeCNF φ,encodeCNF U)
        (result = [] ↔ PEqualNP.ProofComplexity.Satisfiable (clauses φ)) ∧
        (result ≠ [] → ∃ ρ : CNF, encodeCNF ρ = result ∧
          PEqualNP.ProofComplexity.IsRefutation (clauses φ) (ρ.map List.toFinset) ∧
          ∀ c ∈ ρ.map List.toFinset, c ∈ clauses U) := by
  dsimp only
  obtain ⟨search,hsearch,hs⟩ := SuppliedUniverseRefutationSearch
  refine ⟨search,hsearch,fun φ U order hord hstage => ?_⟩
  have hw := hs (encodeCNF φ,encodeCNF U)
  have hn (hnz : search (encodeCNF φ,encodeCNF U) ≠ []) :
      ∃ ρ : CNF, encodeCNF ρ = search (encodeCNF φ,encodeCNF U) ∧
        PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset) ∧
        ∀ c ∈ ρ.map List.toFinset, c ∈ clauseSet U := by
    obtain ⟨φ',U',ρ,hφ,hU,hρ,hπ,hm⟩ := hw.2 hnz
    have eφ := encodeCNF_injective hφ
    have eU := encodeCNF_injective hU
    subst φ' U'
    exact ⟨ρ,hρ,hπ,hm⟩
  refine ⟨⟨?_,?_⟩,hn⟩
  · intro hzero
    by_contra hunsat
    obtain ⟨π,hπ,hm⟩ := EliminationOrderRefutation (clauseSet φ) (clauseSet U) order hord hstage hunsat
    exact (hw.1.mpr ⟨φ,U,rfl,rfl,π,hπ,hm⟩) hzero
  · rintro ⟨a,ha⟩
    by_contra hnz
    obtain ⟨ρ,_,hπ,_⟩ := hn hnz
    obtain ⟨l,hl,_⟩ := PEqualNP.ProofComplexity.Helpers.derivation_sound a hπ.1 ha ∅ hπ.2
    simpa using hl

end PEqualNP.Outside
