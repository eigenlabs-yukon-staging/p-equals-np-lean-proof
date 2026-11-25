import PEqualNP.Outside.ExactRUPRefutationVerifier
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Defs.Classes

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

/-- A measured guard on which all unsatisfiable instances have bounded
RUP traces gives a coNP upper bound for the guarded SAT language. -/
theorem RUPCoverageCoNP (G : Language Bool) (hG : G ∈ P) (q : Polynomial ℕ)
    (coverage : ∀ φ : CNF, encodeCNF φ ∈ G → ¬Satisfiable φ →
      ∃ ρ : CNF, (encodeCNF ρ).length ≤ q.eval (encodeCNF φ).length ∧
        IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map fun c => c.toFinset) ∧
        [] ∈ ρ) :
    (SAT ⊓ G) ∈ coNP := by
  classical
  let R : Set (List Bool × List Bool) := {p | ∃ φ ρ : CNF, encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
    IsRUPRun (clauseSet φ) (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ}
  let A : Language Bool := {x | (∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ G}
  let V : Set (List Bool × List Bool) := {p | p.1 ∉ A ∨ p ∈ R}
  obtain ⟨g,hgs,hg⟩ := hG
  have hr : DecidableInPolyTime encodePair R := ExactRUPRefutationVerifier.1
  obtain ⟨d,hds,hd⟩ := hr
  let test := fun p : List Bool × List Bool => !(wfB p.1 && g p.1) || d p
  have hz := cpt_comp cpt_unpairB1 cpt_wfF
  have hy := cpt_bitFlag (cpt_comp cpt_unpairB1 hg)
  have hx := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hd)
  have hb := cpt_sel hz (cpt_const [true]) (cpt_sel hy (cpt_const [true]) hx)
  have ht := cpt_comp (g := fun w : List Bool => !w.isEmpty) (cpt_comp cpt_pairB hb) bf_cpt_neL
  have he : (fun p : List Bool × List Bool =>
      !(sel (bflag (wfB p.1)) [true] (sel (if g p.1 then [true] else []) [true]
        (if d p then [true] else []))).isEmpty) = test := by
    funext p
    unfold test
    cases wfB p.1 <;> cases g p.1 <;> cases d p <;> rfl
  simp only [unpairB_pairB] at ht
  rw [he] at ht
  have hV : DecidableInPolyTime encodePair V := by
    refine ⟨test,fun p => ?_,ht⟩
    change ((¬ ((∃ φ : CNF, encodeCNF φ = p.1) ∧ p.1 ∈ G)) ∨ p ∈ R) ↔ test p = true
    have hA : ((∃ φ : CNF, encodeCNF φ = p.1) ∧ p.1 ∈ G) ↔ (wfB p.1 && g p.1) = true := by
      rw [Bool.and_eq_true]
      exact and_congr (wfB_iff p.1).symm (hgs p.1)
    have hT : test p = true ↔ ¬ ((wfB p.1 && g p.1) = true) ∨ d p = true := by
      unfold test
      cases (wfB p.1 && g p.1) <;> cases d p <;> decide
    exact (or_congr (not_congr hA) (hds p)).trans hT.symm
  change (SAT ⊓ G)ᶜ ∈ NP
  refine ⟨V,q,hV,fun x => ?_⟩
  change ¬ (x ∈ SAT ∧ x ∈ G) ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ (x,w) ∈ V
  constructor
  · intro hn
    by_cases ha : x ∈ A
    · obtain ⟨⟨φ,rfl⟩,hφ⟩ := ha
      have hu : ¬ Satisfiable φ := fun hs => hn ⟨⟨φ,rfl,hs⟩,hφ⟩
      obtain ⟨ρ,hlen,hr,he⟩ := coverage φ hφ hu
      exact ⟨encodeCNF ρ,hlen,Or.inr ⟨φ,ρ,rfl,rfl,hr,he⟩⟩
    · exact ⟨[],Nat.zero_le _,Or.inl ha⟩
  · rintro ⟨w,_,h⟩ ⟨⟨φ,hφ,hs⟩,hg⟩
    rcases h with hn | ⟨p,ρ,hp,_,hr,he⟩
    · exact hn ⟨⟨φ,hφ⟩,hg⟩
    · have hnot := ExactRUPRefutationVerifier.2 p ρ hr he
      exact hnot (encodeCNF_injective (hφ.trans hp.symm) ▸ hs)

end PEqualNP.Outside
