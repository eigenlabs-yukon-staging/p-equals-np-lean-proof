import PEqualNP.Outside.ExactSuppliedUniverseRefutation
import PEqualNP.Library.L008
import PEqualNP.Library.L046
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

private theorem refutation_excludes (φ : CNF) (π : List FinClause)
    (h : PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) π) : ¬ Satisfiable φ := by
  let ρ := π.map Finset.toList
  have he : ρ.map List.toFinset = π := by
    simp [ρ,List.map_map,Function.comp_def,Finset.toList_toFinset]
  apply ExactResolutionRefutationVerifier.2 φ ρ
  change PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset)
  simpa only [he] using h

/-- A measured finite candidate-universe generator gives a P algorithm
on any guard whose unsatisfiable inputs have a refutation in the universe. -/
theorem MeasuredResolutionUniverseSAT (G : Language Bool) (hG : G ∈ P)
    (generate : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) generate)
    (coverage : ∀ φ : CNF, ∃ U : CNF, generate (encodeCNF φ) = encodeCNF U ∧
      (encodeCNF φ ∈ G → ¬ Satisfiable φ →
        ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
          ∀ d ∈ π, ∃ c ∈ U, c.toFinset = d)) :
    (SAT ⊓ G) ∈ P := by
  classical
  let R : Set (List Bool × List Bool) := {p | ∃ φ U : CNF, encodeCNF φ = p.1 ∧ encodeCNF U = p.2 ∧
    ∃ π : List FinClause, PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) π ∧ ∀ d ∈ π, represented U d}
  have hR : DecidableInPolyTime encodePair R := ExactSuppliedUniverseRefutation
  obtain ⟨test,ht,hct⟩ := hR
  let Q : Language Bool := {x | (x,generate x) ∈ R}
  have hQ : Q ∈ P :=
    ⟨fun x => test (x,generate x),fun x => ht (x,generate x),cpt_comp (cpt_pair cpt_id hg) hct⟩
  let E : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  have hW := cpt_comp (g := fun x : List Bool => !x.isEmpty) cpt_wfF bf_cpt_neL
  have he : (fun x => !(bflag (wfB x)).isEmpty) = wfB := by
    funext x
    cases wfB x <;> rfl
  rw [he] at hW
  have hE : E ∈ P := ⟨wfB,fun x => (wfB_iff x).symm,hW⟩
  have h := L046 (E ⊓ G) Qᶜ (L046 E G hE hG) (L008 Q hQ)
  have hL : SAT ⊓ G = (E ⊓ G) ⊓ Qᶜ := by
    ext x
    change ((∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ) ∧ x ∈ G) ↔
      ((∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ G) ∧ x ∉ Q
    constructor
    · rintro ⟨⟨φ,rfl,hs⟩,hg⟩
      refine ⟨⟨⟨φ,rfl⟩,hg⟩,?_⟩
      rintro ⟨p,U,hp,_,π,hπ,_⟩
      exact refutation_excludes p π hπ ((encodeCNF_injective hp).symm ▸ hs)
    · rintro ⟨⟨⟨φ,rfl⟩,hg⟩,hQ⟩
      refine ⟨⟨φ,rfl,?_⟩,hg⟩
      by_contra hs
      obtain ⟨U,hU,hcovers⟩ := coverage φ
      obtain ⟨π,hπ,hrepr⟩ := hcovers hg hs
      exact hQ ⟨φ,U,rfl,hU.symm,π,hπ,hrepr⟩
  rwa [hL]

end PEqualNP.Outside
