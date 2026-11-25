import PEqualNP.Outside.MeasuredRankedBackdoorWalk
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Library.L046

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search

private theorem budget_exact (q : Polynomial ℕ) (keep : Bool) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ k : ℕ, 6^k ≤ q.eval x.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧
      Satisfiable (if keep then φ else [])} ∈ P := by
  obtain ⟨walk,hwalk,hws⟩ := MeasuredRankedBackdoorWalk
  let clock := fun x : List Bool => true :: List.replicate (q.eval x.length) true
  let g := fun z : List Bool × List Bool =>
    if walk (pairB (clock z.2) (pairB z.1 (pairB z.2 (if keep then z.2 else [])))) then [true] else []
  let R : Set (List Bool × List Bool) := {z | z.2 ≠ []}
  have hR : DecidableInPolyTime encodePair R :=
    ⟨fun z => !z.2.isEmpty,fun _ => by simp [R,Bool.not_eq_true',List.isEmpty_eq_false_iff],
      cpt_comp (g := fun w : List Bool => !w.isEmpty) cpt_snd bf_cpt_neL⟩
  have hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) clock :=
    cpt_cons1 true (L055 q)
  have hres : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun r => if keep then (unpairB r).2 else []) := by
    cases keep
    · exact cpt_const []
    · exact cpt_unpairB2
  have harg := cpt_pairB2 (cpt_comp cpt_unpairB2 hc)
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 hres))
  have hflag := cpt_bitFlag (cpt_comp harg hwalk)
  have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) g := by
    have hraw := cpt_comp cpt_pairB hflag
    simpa only [unpairB_pairB,g] using hraw
  let D : Language Bool := {x | ∃ i < (clock x).length, (x,g (List.replicate i true,x)) ∈ R}
  let E : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x}
  have hD : D ∈ P := IndexedWitnessProjection R hR clock hc g hg
  have hcan := cpt_comp (g := fun w : List Bool => !w.isEmpty) cpt_wfF bf_cpt_neL
  have hc' : (fun w => !(bflag (wfB w)).isEmpty) = wfB := by
    funext w
    cases wfB w <;> rfl
  rw [hc'] at hcan
  have hE : E ∈ P := ⟨wfB,fun w => (wfB_iff w).symm,hcan⟩
  have hDspec (φ : CNF) :
      encodeCNF φ ∈ D ↔
        (∃ k : ℕ, 6^k ≤ q.eval (encodeCNF φ).length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
          IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧
        Satisfiable (if keep then φ else []) := by
    let p := if keep then φ else ([] : CNF)
    have hsub : p.Sublist φ := by
      cases keep
      · exact List.nil_sublist _
      · exact List.Sublist.refl _
    have hx : encodeCNF p = (if keep then encodeCNF φ else []) := by cases keep <;> rfl
    have hl : (clock (encodeCNF φ)).length = q.eval (encodeCNF φ).length + 1 := by simp [clock]
    have hb : 1 ≤ (clock (encodeCNF φ)).length := by rw [hl]; omega
    have hs := hws (clock (encodeCNF φ)) φ p hb hsub
    rw [hx,hl] at hs
    change (∃ i < (clock (encodeCNF φ)).length, g (List.replicate i true,encodeCNF φ) ≠ []) ↔ _
    rw [hl]
    apply Iff.trans _ hs
    have hd (i : ℕ) :
        g (List.replicate i true,encodeCNF φ) ≠ [] ↔
        walk (pairB (clock (encodeCNF φ)) (pairB (List.replicate i true)
          (pairB (encodeCNF φ) (if keep then encodeCNF φ else [])))) = true := by
      unfold g
      cases walk (pairB (clock (encodeCNF φ)) (pairB (List.replicate i true)
          (pairB (encodeCNF φ) (if keep then encodeCNF φ else [])))) <;> decide
    exact exists_congr (fun i => and_congr_right (fun _ => hd i))
  have ee :
      {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
        (∃ k : ℕ, 6^k ≤ q.eval x.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
          IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧
        Satisfiable (if keep then φ else [])} = E ⊓ D := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧ _) ↔ (∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ D
    constructor
    · rintro ⟨φ,rfl,h⟩
      exact ⟨⟨φ,rfl⟩,(hDspec φ).mpr h⟩
    · rintro ⟨⟨φ,rfl⟩,h⟩
      exact ⟨φ,rfl,(hDspec φ).mp h⟩
  rw [ee]
  exact L046 E D hE hD

/-- A single reference P machine per polynomial clock recognizes and solves
the variable-deletion SAT class with a logarithmic deletion budget. -/
theorem ExactPolynomialBudgetTwoSATBackdoor (q : Polynomial ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∃ k : ℕ, 6^k ≤ q.eval x.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))} ∈ P ∧
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (∃ k : ℕ, 6^k ≤ q.eval x.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧ Satisfiable φ} ∈ P := by
  have hs : Satisfiable [] := ⟨fun _ => false,rfl⟩
  exact ⟨by simpa [hs] using budget_exact q false,by simpa using budget_exact q true⟩

end PEqualNP.Outside
