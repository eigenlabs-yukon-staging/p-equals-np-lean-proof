import PEqualNP.Outside.CNFComponentCorrect

namespace PEqualNP.Outside

open PEqualNP.Search

/-- The clause list is satisfiable exactly when it has no empty clause and
each variable co-occurrence component is satisfiable. -/
theorem CNFComponentFactorization (φ : CNF) :
    let part := fun (x : ℕ) => φ.filter (fun c =>
      @decide (∃ m ∈ c, Relation.ReflTransGen (fun a b : ℕ =>
        ∃ d ∈ φ, a ∈ d.map Prod.fst ∧ b ∈ d.map Prod.fst) x m.1) (Classical.propDecidable _))
    Satisfiable φ ↔ [] ∉ φ ∧ ∀ x, Satisfiable (part x) :=
  components_sat_iff φ

end PEqualNP.Outside
