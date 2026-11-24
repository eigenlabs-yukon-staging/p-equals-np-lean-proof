import PEqualNP.Outside.HornSATSublanguageInP
import PEqualNP.Outside.PositivePairSemantics

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search
open PEqualNP.Outside.PositivePairMachine (obstruction obstruction_cpt)
open PEqualNP.Outside.PositivePairSemantics (firstBad firstBad_none encodeNames obstruction_enc)

private theorem guard_correct (φ : CNF) :
    obstruction (encodeCNF φ, []) = [] ↔ ∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1 := by
  change obstruction (encodeCNF φ, PEqualNP.Outside.CnfRestrictionSemantics.names []) = [] ↔ _
  have he : firstBad [] φ = none ↔ ∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1 := by
    simpa using firstBad_none [] φ
  rw [obstruction_enc, ← he]
  cases h : firstBad [] φ
  · simp
  · simp [encodeNames, pairB]

theorem PEqualNP.Outside.HornSATInP :
    ({x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1) ∧ Satisfiable φ} : Language Bool) ∈ P := by
  obtain ⟨L, ⟨dec, hd, ht⟩, hsound, hcomplete⟩ := HornSATSublanguageInP
  let guard (x : List Bool) := obstruction (x, [])
  let answer (x : List Bool) :=
    (sel (guard x) (sel (bflag (dec x)) [true] []) [true]).isEmpty
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) guard := by
    have h := cpt_comp (cpt_pair cpt_id (cpt_const [])) obstruction_cpt
    exact h
  have htime : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool answer := by
    have h := cpt_comp (cpt_sel hg (cpt_sel (cpt_bitFlag ht) (cpt_const [true]) (cpt_const []))
      (cpt_const [true])) cpt_isEmpty
    exact h
  have hans (x : List Bool) : answer x = true ↔ x ∈ L ∧ guard x = [] := by
    refine Iff.trans ?_ (and_congr (hd x).symm Iff.rfl)
    by_cases h : guard x = [] <;> cases hb : dec x <;> simp [answer, sel, h, hb, bflag]
  refine ⟨answer, ?_, htime⟩
  intro x
  rw [hans]
  constructor
  · rintro ⟨φ, rfl, hh, hs⟩
    exact ⟨(hcomplete φ hh).mpr hs, (guard_correct φ).mpr hh⟩
  · rintro ⟨h, hg⟩
    obtain ⟨φ, rfl, hs⟩ := hsound x h
    exact ⟨φ, rfl, (guard_correct φ).mp hg, hs⟩
