import PEqualNP.Library.L046
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Outside.CNFThreeClausePacking
import PEqualNP.Outside.LogarithmicThreeClauseSAT
import PEqualNP.Outside.MeasuredWidthThree
import PEqualNP.Outside.MeasuredRecordCount
import PEqualNP.Outside.UnaryPowerBudget

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

private abbrev Triple := Literal × Literal × Literal

private def triples (φ : CNF) : List Triple :=
  (φ.filterMap (fun c => if c.length = 3 then
    some (c.getD 0 (0,false), c.getD 1 (0,false), c.getD 2 (0,false)) else none)).reverse

private def unitGroup (g : Triple) : List Bool :=
  pairB (encodeClause [g.1]) (pairB (encodeClause [g.2.1]) (encodeClause [g.2.2]))

private theorem count_triples (φ : CNF) :
    (triples φ).length = (φ.filter (fun c => c.length = 3)).length := by
  rw [triples, List.length_reverse]
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      by_cases h : c.length = 3 <;> simpa [h] using ih

/-- Exact P membership for the well-formed reference 3-CNF language under the
polynomial bound on the branching space of its ternary clauses. -/
theorem ExactLogarithmicThreeClauseSAT (q : Polynomial ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ IsKCNF 3 φ ∧
      2 ^ (2 * (φ.filter (fun c => c.length = 3)).length + 1) ≤ q.eval x.length ∧
      Satisfiable φ} ∈ P := by
  obtain ⟨pack, hpack, hshape⟩ := CNFThreeClausePacking
  obtain ⟨count, hcount, hcountSpec⟩ := MeasuredRecordCount
  obtain ⟨D, hD, hdec⟩ := LogarithmicThreeClauseSAT q
  let valid : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧ IsKCNF 3 φ}
  let countGroups := fun x => count (unpairB (pack x)).2
  let exponent := fun x => true :: (countGroups x ++ countGroups x)
  let budget := fun x : List Bool => List.replicate (q.eval x.length) true
  let guard : Language Bool := {x | 2 ^ (exponent x).length ≤ (budget x).length}
  have hgroups : ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) countGroups :=
    cpt_comp (cpt_unpairB2_1 hpack) hcount
  have hexp : ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) exponent := cpt_cons1 true (cpt_app2 hgroups hgroups)
  have hguard : guard ∈ P := by
    obtain ⟨g, hg, hcg⟩ := UnaryPowerBudget
    refine ⟨fun x => g (exponent x, budget x), fun x => ?_,
      cpt_comp (cpt_pair hexp (L055 q)) hcg⟩
    exact hg (exponent x, budget x)
  have hcap (φ : CNF) (hφ : IsKCNF 3 φ) :
      encodeCNF φ ∈ guard ↔ 2 ^ (2 * (φ.filter (fun c => c.length = 3)).length + 1) ≤
        q.eval (encodeCNF φ).length := by
    let small := (φ.filter (fun c => c.length ≤ 2)).reverse
    have hpack' : pack (encodeCNF φ) =
        pairB (encodeCNF small) (((triples φ).map unitGroup).foldr pairB []) := by
      rw [List.foldr_map]
      exact hshape φ hφ
    have hsize : countGroups (encodeCNF φ) = List.replicate (triples φ).length true := by
      simp only [countGroups, hpack', unpairB_pairB]
      have hpair : pairB = (fun word rest : List Bool =>
          List.replicate word.length true ++ false :: (word ++ rest)) := rfl
      rw [hpair]
      simpa only [List.length_map] using hcountSpec ((triples φ).map unitGroup)
    change 2 ^ (exponent (encodeCNF φ)).length ≤ (budget (encodeCNF φ)).length ↔ _
    simp only [exponent, budget, hsize, List.length_cons, List.length_append, List.length_replicate]
    rw [count_triples]
    have he (n : ℕ) : n + n + 1 = 2 * n + 1 := by omega
    rw [he]
  have h := L046 (valid ⊓ guard) D (L046 valid guard MeasuredWidthThree hguard) hD
  have hset : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ IsKCNF 3 φ ∧
      2 ^ (2 * (φ.filter (fun c => c.length = 3)).length + 1) ≤ q.eval x.length ∧
      Satisfiable φ} = valid ⊓ guard ⊓ D := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧ IsKCNF 3 φ ∧
      2 ^ (2 * (φ.filter (fun c => c.length = 3)).length + 1) ≤ q.eval x.length ∧ Satisfiable φ) ↔
      ((∃ φ : CNF, encodeCNF φ = x ∧ IsKCNF 3 φ) ∧ x ∈ guard) ∧ x ∈ D
    constructor
    · rintro ⟨φ, rfl, hφ, hbudget, hsat⟩
      exact ⟨⟨⟨φ,rfl,hφ⟩,(hcap φ hφ).mpr hbudget⟩,(hdec φ hφ hbudget).mpr hsat⟩
    · rintro ⟨⟨⟨φ,rfl,hφ⟩, hbudget⟩, hDφ⟩
      have hbound := (hcap φ hφ).mp hbudget
      exact ⟨φ,rfl,hφ,hbound,(hdec φ hφ hbound).mp hDφ⟩
  rwa [hset]

end PEqualNP.Outside
