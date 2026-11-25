import PEqualNP.Library.L055
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Outside.MeasuredCNFPartition
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Outside.MeasuredMixedRadixUnits

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

private theorem partition_eval (test : List Bool → Bool) (φ : CNF) (σ : Assignment) :
    φ.eval σ = true ↔
      CNF.eval σ ((φ.filter (fun c => test (encodeClause c))).reverse) = true ∧
      CNF.eval σ ((φ.filter (fun c => !test (encodeClause c))).reverse) = true := by
  simp only [CNF.eval, List.all_eq_true, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun c hc => h c hc.1, fun c hc => h c hc.1⟩
  · rintro ⟨h₁,h₂⟩ c hc
    cases h : test (encodeClause c)
    · exact h₂ c ⟨hc,by simp [h]⟩
    · exact h₁ c ⟨hc,h⟩

private theorem encode_append (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF, List.flatMap_append]

private theorem eval_append (σ : Assignment) (a b : CNF) :
    (a ++ b).eval σ = true ↔ a.eval σ = true ∧ b.eval σ = true := by
  simp [CNF.eval, List.all_append]

/-- Any measured clause predicate that includes empty and unit clauses can use
mixed-radix branching over its excluded clauses if its base has a P decider. -/
theorem ClausePartitionProductSAT (test : List Bool → Bool)
    (ht : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test)
    (B : Language Bool) (hB : B ∈ P)
    (hunit : ∀ c : Clause, c.length ≤ 1 → test (encodeClause c) = true)
    (hbase : ∀ φ : CNF, (∀ c ∈ φ, test (encodeClause c) = true) →
       (encodeCNF φ ∈ B ↔ Satisfiable φ))
    (q : Polynomial ℕ) :
    ∃ D : Language Bool, D ∈ P ∧ ∀ φ : CNF,
      ((φ.filter (fun c => !test (encodeClause c))).map List.length).prod ≤ q.eval (encodeCNF φ).length →
        (encodeCNF φ ∈ D ↔ Satisfiable φ) := by
  obtain ⟨pack,hpack,hshape⟩ := MeasuredCNFPartition test ht
  obtain ⟨choose,hchoose,hsound,hcomplete⟩ := MeasuredMixedRadixUnits
  obtain ⟨sat,hsat,hc⟩ := hB
  let relation : Set (List Bool × List Bool) := {z | z.2 ∈ B}
  have hrel : DecidableInPolyTime encodePair relation :=
    ⟨fun z => sat z.2,fun z => hsat z.2,cpt_comp cpt_snd hc⟩
  let clock := fun x : List Bool => List.replicate (q.eval x.length) true
  let gen := fun z : List Bool × List Bool =>
    (unpairB (pack z.2)).1 ++ choose (z.1,(unpairB (pack z.2)).2)
  have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) gen := by
    have hpacked := cpt_comp cpt_snd hpack
    have hbase := cpt_comp hpacked cpt_unpairB1
    have hwide := cpt_comp hpacked cpt_unpairB2
    have hunit := cpt_comp (cpt_pairG cpt_fst hwide) hchoose
    exact cpt_comp (cpt_pairG hbase hunit) cpt_append
  let D : Language Bool := {x | ∃ i < (clock x).length, (x, gen (List.replicate i true,x)) ∈ relation}
  refine ⟨D,IndexedWitnessProjection relation hrel clock (L055 q) gen hg,fun φ hbudget => ?_⟩
  let base := (φ.filter (fun c => test (encodeClause c))).reverse
  let wide := (φ.filter (fun c => !test (encodeClause c))).reverse
  let x := encodeCNF φ
  have hwidth : ∀ c ∈ base, test (encodeClause c) = true := by
    intro c hc
    exact (List.mem_filter.mp (List.mem_reverse.mp hc)).2
  have hgood (units : CNF) (h : IsKCNF 1 units) : ∀ c ∈ base ++ units, test (encodeClause c) = true := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hwidth c hc
    · exact hunit c (h c hc)
  have hlength : (wide.map List.length).prod = ((φ.filter (fun c => !test (encodeClause c))).map List.length).prod := by
    simp [wide, List.map_reverse, List.prod_reverse]
  have hpack' : pack x = pairB (encodeCNF base) (encodeCNF wide) := hshape φ
  have hgen (i : ℕ) : gen (List.replicate i true,x) =
      encodeCNF base ++ choose (List.replicate i true,encodeCNF wide) := by
    simp only [gen,hpack',unpairB_pairB]
  change (∃ i < (clock x).length, gen (List.replicate i true,x) ∈ B) ↔ _
  constructor
  · rintro ⟨i,_,hi⟩
    obtain ⟨units,hwidth',he,hu⟩ := hsound wide (List.replicate i true)
    rw [hgen,he,← encode_append] at hi
    obtain ⟨σ,hF⟩ := (hbase _ (hgood _ hwidth')).mp hi
    obtain ⟨hb,hunit'⟩ := (eval_append _ _ _).mp hF
    exact ⟨σ,(partition_eval test φ σ).mpr ⟨hb,hu σ hunit'⟩⟩
  · rintro ⟨σ,hφ⟩
    obtain ⟨hb,hw⟩ := (partition_eval test φ σ).mp hφ
    obtain ⟨i,hi,units,he,hunit⟩ := hcomplete wide σ hw
    obtain ⟨units',hunitWidth,he',_⟩ := hsound wide (List.replicate i true)
    have hu : units' = units := PEqualNP.Library.SearchHelpers.encodeCNF_injective (he'.symm.trans he)
    subst units'
    refine ⟨i, ?_, ?_⟩
    · simp only [clock, x, List.length_replicate]
      rw [hlength] at hi
      exact hi.trans_le hbudget
    · rw [hgen,he,← encode_append]
      exact (hbase _ (hgood _ hunitWidth)).mpr ⟨σ,(eval_append _ _ _).mpr ⟨hb,hunit⟩⟩

end PEqualNP.Outside
