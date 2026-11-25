import PEqualNP.Library.L046
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Outside.MeasuredCNFPartition
import PEqualNP.Outside.MeasuredCappedClauseProduct
import PEqualNP.Outside.ClausePartitionProductSAT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

/-- The exact product-bounded exception language of a measured clause family in P. -/
theorem ExactClausePartitionProductSAT (test : List Bool → Bool)
    (ht : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test)
    (B : Language Bool) (hB : B ∈ P)
    (hunit : ∀ c : Clause, c.length ≤ 1 → test (encodeClause c) = true)
    (hbase : ∀ φ : CNF, (∀ c ∈ φ, test (encodeClause c) = true) →
       (encodeCNF φ ∈ B ↔ Satisfiable φ))
    (q : Polynomial ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ((φ.filter (fun c => !test (encodeClause c))).map List.length).prod ≤ q.eval x.length ∧
      Satisfiable φ} ∈ P := by
  obtain ⟨pack,hpack,hpackSpec⟩ := MeasuredCNFPartition test ht
  obtain ⟨product,hproduct,hproductSpec⟩ := MeasuredCappedClauseProduct
  obtain ⟨D,hD,hdec⟩ := ClausePartitionProductSAT test ht B hB hunit hbase q
  let valid : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  let budget := fun x : List Bool => List.replicate (q.eval x.length) true
  let cap := fun x => true :: budget x
  let prod := fun x => product (cap x, (unpairB (pack x)).2)
  let guard : Language Bool := {x | (prod x).length ≤ (budget x).length}
  have hvalid : valid ∈ P := by
    have hm := cpt_comp (g := fun l : List Bool => !l.isEmpty)
      PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF bf_cpt_neL
    have e : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
      funext s
      cases wfB s <;> rfl
    rw [e] at hm
    exact ⟨wfB, fun s => (wfB_iff s).symm, hm⟩
  have hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) prod :=
    cpt_comp (cpt_pair (cpt_cons1 true (L055 q)) (cpt_unpairB2_1 hpack)) hproduct
  have hg : guard ∈ P :=
    ⟨fun x => decide ((prod x).length ≤ (budget x).length),fun _ => decide_eq_true_iff.symm,
      cpt_comp (cpt_pair (L055 q) hp) LenCmp.lenLE_polyTime⟩
  have hguard (φ : CNF) : encodeCNF φ ∈ guard ↔
      ((φ.filter (fun c => !test (encodeClause c))).map List.length).prod ≤ q.eval (encodeCNF φ).length := by
    let base := (φ.filter (fun c => test (encodeClause c))).reverse
    let wide := (φ.filter (fun c => !test (encodeClause c))).reverse
    have hshape : pack (encodeCNF φ) = pairB (encodeCNF base) (encodeCNF wide) := hpackSpec φ
    change (prod (encodeCNF φ)).length ≤ (budget (encodeCNF φ)).length ↔ _
    simp only [prod, hshape, unpairB_pairB, hproductSpec, cap, budget, List.length_cons,
      List.length_replicate, wide, List.map_reverse, List.prod_reverse]
    omega
  have h := L046 (valid ⊓ guard) D (L046 valid guard hvalid hg) hD
  have e : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ((φ.filter (fun c => !test (encodeClause c))).map List.length).prod ≤ q.eval x.length ∧ Satisfiable φ} =
      valid ⊓ guard ⊓ D := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧
      ((φ.filter (fun c => !test (encodeClause c))).map List.length).prod ≤ q.eval x.length ∧ Satisfiable φ) ↔
      ((∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ guard) ∧ x ∈ D
    constructor
    · rintro ⟨φ,rfl,hb,hs⟩
      exact ⟨⟨⟨φ,rfl⟩,(hguard φ).mpr hb⟩,(hdec φ hb).mpr hs⟩
    · rintro ⟨⟨⟨φ,rfl⟩,hb⟩,hs⟩
      have hb' := (hguard φ).mp hb
      exact ⟨φ,rfl,hb',(hdec φ hb').mp hs⟩
  rwa [e]

end PEqualNP.Outside
