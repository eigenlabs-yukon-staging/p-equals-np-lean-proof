import PEqualNP.Outside.ExactRUPRefutationVerifier
import PEqualNP.Library.Machines.LenLE

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

/-- Verify a canonical RUP refutation and its encoded size budget in the
same measured paired computation. -/
theorem MeasuredBoundedRUPCheck (q : Polynomial ℕ) :
    DecidableInPolyTime encodePair
      {p : List Bool × List Bool | p.2.length ≤ q.eval p.1.length ∧
        ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
        IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ} := by
  let R : Set (List Bool × List Bool) := {p | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
    IsRUPRun (clauseSet φ) (ρ.map List.toFinset) ∧ [] ∈ ρ}
  have hR : DecidableInPolyTime encodePair R := ExactRUPRefutationVerifier.1
  obtain ⟨verify,hv,hvc⟩ := hR
  let budget := fun x : List Bool => List.replicate (q.eval x.length) true
  let bound := fun p : List Bool × List Bool => decide (p.2.length ≤ (budget p.1).length)
  let test := fun p => bound p && verify p
  have hb : ComputableInPolyTime encodePair Computability.encodeBool bound :=
    cpt_comp (cpt_pairG (cpt_comp cpt_fst (L055 q)) cpt_snd) LenCmp.lenLE_polyTime
  have hp := cpt_pair cpt_unpairB1 cpt_unpairB2
  have hr := cpt_sel (cpt_bitFlag (cpt_comp hp hb)) (cpt_const []) (cpt_bitFlag (cpt_comp hp hvc))
  have ht := cpt_comp (g := fun x : List Bool => !x.isEmpty) (cpt_comp cpt_pairB hr) bf_cpt_neL
  have he : (fun p : List Bool × List Bool => !(sel (if bound p then [true] else [])
      [] (if verify p then [true] else [])).isEmpty) = test := by
    funext p
    unfold test
    cases bound p <;> cases verify p <;> rfl
  simp only [unpairB_pairB] at ht
  rw [he] at ht
  refine ⟨test,fun p => ?_,ht⟩
  change (p.2.length ≤ q.eval p.1.length ∧ p ∈ R) ↔ test p = true
  simp only [test,bound,Bool.and_eq_true,decide_eq_true_eq,budget,List.length_replicate]
  exact and_congr_right (fun _ => hv p)

end PEqualNP.Outside
