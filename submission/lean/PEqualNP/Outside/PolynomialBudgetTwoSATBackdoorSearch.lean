import PEqualNP.Outside.ExactPolynomialBudgetTwoSATBackdoor
import PEqualNP.Outside.SparseVariableSATSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

private theorem mono_eval (q : Polynomial ℕ) : Monotone q.eval := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      intro a b hab
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add (hp hab) (hq hab)
  | monomial i c =>
      intro a b hab
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab _)

private theorem unit_width (xs : List ℕ) (ls : List Literal) :
    IsKCNF 2 ((ls.map (fun l => [l])).map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) := by
  intro c hc
  rw [List.map_map,List.mem_map] at hc
  obtain ⟨l,_,rfl⟩ := hc
  exact (List.length_filter_le (fun a : Literal => decide (a.1 ∉ xs)) [l]).trans (by simp)

private theorem append_units (q : Polynomial ℕ) (φ : CNF) (ls : List Literal)
    (h : ∃ k : ℕ, 6^k ≤ q.eval (encodeCNF φ).length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
      IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) :
    ∃ k : ℕ, 6^k ≤ q.eval (encodeCNF (φ ++ ls.map (fun l => [l]))).length + 1 ∧
      ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 ((φ ++ ls.map (fun l => [l])).map
          (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) := by
  obtain ⟨k,hk,xs,hxs,hw⟩ := h
  have hlen : (encodeCNF φ).length ≤ (encodeCNF (φ ++ ls.map (fun l => [l]))).length := by
    simp only [encodeCNF,List.flatMap_append,List.length_append]
    omega
  refine ⟨k,hk.trans (Nat.add_le_add_right (mono_eval q hlen) _),xs,hxs,fun c hc => ?_⟩
  rw [List.map_append,List.mem_append] at hc
  exact hc.elim (hw c) (unit_width xs ls c)

/-- Sparse witness recovery for the uniform measured solver with polynomially
many branch ranks. Appending any unit constraints preserves the usable budget. -/
theorem PolynomialBudgetTwoSATBackdoorSearch (q : Polynomial ℕ) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∃ k : ℕ, 6^k ≤ q.eval (encodeCNF φ).length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    (∃ k : ℕ, 6^k ≤ q.eval x.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
      IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧ Satisfiable φ}
  obtain ⟨search,hs,hc⟩ := SparseVariableSATSearch D (ExactPolynomialBudgetTwoSATBackdoor q).2
  refine ⟨search,hs,fun φ h => hc φ (fun ls => ?_)⟩
  let ψ : CNF := φ ++ ls.map (fun l => [l])
  change encodeCNF ψ ∈ D ↔ Satisfiable ψ
  constructor
  · rintro ⟨f,henc,_,hs⟩
    exact encodeCNF_injective henc ▸ hs
  · intro hs
    exact ⟨ψ,rfl,append_units q φ ls h,hs⟩

end PEqualNP.Outside
