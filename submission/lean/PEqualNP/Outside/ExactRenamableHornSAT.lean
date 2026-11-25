import PEqualNP.Outside.MeasuredHornPairEncoding
import PEqualNP.Outside.MeasuredCNFRenaming
import PEqualNP.Outside.SparseVariableSATSearch
import PEqualNP.Outside.ExactHornSAT
import PEqualNP.Library.L030
import PEqualNP.Library.L016
import PEqualNP.Library.L046
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

private theorem ksat_iff (φ : CNF) (h : IsKCNF 2 φ) :
    encodeCNF φ ∈ KSAT 2 ↔ Satisfiable φ := by
  constructor
  · rintro ⟨G,_,he,hg⟩
    exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective he) ▸ hg
  · intro hg
    exact ⟨φ,h,rfl,hg⟩

private theorem append_units_width (φ : CNF) (h : IsKCNF 2 φ) (ls : List Literal) :
    IsKCNF 2 (φ ++ ls.map (fun l => [l])) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc
  · obtain ⟨l,_,rfl⟩ := List.mem_map.mp hc
    simp

private theorem canonical_in_p : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x} ∈ P := by
  have hc := cpt_comp (g := fun l : List Bool => !l.isEmpty)
    PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF bf_cpt_neL
  have he : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
    funext s
    cases wfB s <;> rfl
  rw [he] at hc
  exact ⟨wfB,fun s => (wfB_iff s).symm,hc⟩

/-- Satisfiable reference CNF encodings admitting a Horn sign renaming form an exact P language. -/
theorem ExactRenamableHornSAT :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1) ∧
      Satisfiable φ} ∈ P := by
  obtain ⟨constraints,hmeta,hspec⟩ := measuredHornPairEncoding_semantics
  obtain ⟨rename,hren,hsem⟩ := measuredCNFRenaming_semantics
  obtain ⟨find,hfind,hsearch⟩ := SparseVariableSATSearch (KSAT 2) L030
  let H : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
      (∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧ Satisfiable φ}
  let V : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  let R : Language Bool := {x | constraints x ∈ KSAT 2}
  let renamed := fun x => rename (x,find (constraints x))
  let A : Language Bool := {x | renamed x ∈ H}
  have hR : R ∈ P := L016 R (KSAT 2) ⟨constraints,hmeta,fun _ => Iff.rfl⟩ L030
  have hrename : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) renamed :=
    cpt_comp (cpt_pair cpt_id (cpt_comp hmeta hfind)) hren
  have hA : A ∈ P := L016 A H ⟨renamed,hrename,fun _ => Iff.rfl⟩ ExactHornSAT
  have h : V ⊓ R ⊓ A ∈ P := L046 (V ⊓ R) A (L046 V R canonical_in_p hR) hA
  have hrename_mem (φ : CNF) :
      encodeCNF φ ∈ R ↔ ∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1 := by
    change constraints (encodeCNF φ) ∈ KSAT 2 ↔ _
    rw [hspec,ksat_iff _ (pair_constraints_width φ)]
    apply exists_congr
    intro flip
    rw [pair_constraints_truth]
    constructor
    · intro h c hc
      exact h _ (List.mem_map_of_mem hc)
    · intro h c hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact h d hd
  have hSatFor (φ : CNF) (hr : encodeCNF φ ∈ R) :
      encodeCNF φ ∈ A ↔ Satisfiable φ := by
    let F := hornRenamingConstraints φ
    have hF : IsKCNF 2 F := pair_constraints_width φ
    have hm : constraints (encodeCNF φ) = encodeCNF F := hspec φ
    have hs : Satisfiable F := (ksat_iff F hF).mp (hm ▸ hr)
    obtain ⟨vs,hcode,_,hEval⟩ := hsearch F (fun ls => ksat_iff _ (append_units_width F hF ls)) hs
    let flip : Assignment := fun i => decide (i ∈ vs)
    have ha : asg (find (constraints (encodeCNF φ))) = flip := by
      rw [hm,hcode]
      change asg (vs.flatMap vcode) = flip
      funext i
      rw [Bool.eq_iff_iff, asg_codes]
      simp [flip]
    have htarget : renamed (encodeCNF φ) = encodeCNF (flipFormula flip φ) := by
      simp only [renamed,hsem,ha]
    have hHorn := (pair_constraints_truth φ flip).mp hEval
    change renamed (encodeCNF φ) ∈ H ↔ Satisfiable φ
    rw [htarget,← flip_preserves_sat flip φ]
    constructor
    · rintro ⟨G,hG,_,hsG⟩
      exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective hG) ▸ hsG
    · intro hsG
      exact ⟨flipFormula flip φ,rfl,hHorn,hsG⟩
  have hset : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1) ∧
      Satisfiable φ} = V ⊓ R ⊓ A := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧
      (∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1) ∧
      Satisfiable φ) ↔ ((∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ R) ∧ x ∈ A
    constructor
    · rintro ⟨φ,rfl,hr,hs⟩
      have hR' := (hrename_mem φ).mpr hr
      exact ⟨⟨⟨φ,rfl⟩,hR'⟩,(hSatFor φ hR').mpr hs⟩
    · rintro ⟨⟨⟨φ,rfl⟩,hr⟩,ha⟩
      exact ⟨φ,rfl,(hrename_mem φ).mp hr,(hSatFor φ hr).mp ha⟩
  rwa [hset]

end PEqualNP.Outside
