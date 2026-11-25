import PEqualNP.Outside.MeasuredHornPairEncoding
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

/-- Recognition of canonical CNF encodings that admit a Horn sign renaming is in P. -/
theorem ExactRenamableHornGuard :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1} ∈ P := by
  obtain ⟨make,hm,hs⟩ := MeasuredHornPairEncoding
  let V : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  let R : Language Bool := {x | make x ∈ KSAT 2}
  have hv : V ∈ P := by
    have h := cpt_comp (g := fun l : List Bool => !l.isEmpty)
      PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF bf_cpt_neL
    have he : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
      funext s
      cases wfB s <;> rfl
    rw [he] at h
    exact ⟨wfB,fun s => (wfB_iff s).symm,h⟩
  have hr : R ∈ P := L016 R (KSAT 2) ⟨make,hm,fun x => Iff.rfl⟩ L030
  have h := L046 V R hv hr
  have hsem (φ : CNF) : encodeCNF φ ∈ R ↔
      ∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1 := by
    obtain ⟨F,hwidth,hF,hchar⟩ := hs φ
    change make (encodeCNF φ) ∈ KSAT 2 ↔ _
    rw [hF]
    constructor
    · rintro ⟨G,_,he,σ,hσ⟩
      have e := PEqualNP.Library.SearchHelpers.encodeCNF_injective he
      subst G
      exact ⟨σ,(hchar σ).mp hσ⟩
    · rintro ⟨σ,hσ⟩
      exact ⟨F,hwidth,rfl,σ,(hchar σ).mpr hσ⟩
  have hset : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1} = V ⊓ R := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧ ∃ flip : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1) ↔
      (∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ R
    constructor
    · rintro ⟨φ,rfl,hφ⟩
      exact ⟨⟨φ,rfl⟩,(hsem φ).mpr hφ⟩
    · rintro ⟨⟨φ,rfl⟩,hφ⟩
      exact ⟨φ,rfl,(hsem φ).mp hφ⟩
  rwa [hset]

end PEqualNP.Outside
