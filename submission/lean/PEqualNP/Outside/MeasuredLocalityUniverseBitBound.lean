import PEqualNP.Outside.MeasuredLocalityClauseUniverse

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Search

/-- The signed window catalogue has a linear bound on encoded length as
well as on its number of rows, for every fixed first-occurrence radius. -/
theorem MeasuredLocalityUniverseBitBound (k : ℕ) :
    let window := fun (c : Clause) (i : ℕ) =>
      ((c.drop i).take (k+1)).flatMap (fun l => [l,(l.1,!l.2)])
    ∃ gen : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen ∧
      ∀ c : Clause, ∃ U : CNF, gen (encodeClause c) = encodeCNF U ∧
        U.length ≤ 1 + c.length * 2^(2*(k+1)) ∧
        (encodeCNF U).length ≤ 2 + 2^(2*(k+1)) * (2*(k+2)*(encodeClause c).length) ∧
        ∀ d : Clause, d ∈ U ↔ d = [] ∨ ∃ i < c.length, d.Sublist (window c i) :=
  measuredLocalityClauseUniverse_bounded k

end PEqualNP.Outside
