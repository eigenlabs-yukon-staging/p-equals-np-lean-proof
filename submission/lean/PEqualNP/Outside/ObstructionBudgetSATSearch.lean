import PEqualNP.Outside.ExactObstructionBudgetSAT
import PEqualNP.Outside.SparseVariableSATSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

private theorem eval_mono (q : Polynomial ℕ) : Monotone q.eval := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      intro x y h
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add (hp h) (hq h)
  | monomial i c =>
      intro x y h
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

/-- Sparse witness recovery from a bounded obstruction, when appending
clauses of width zero or one preserves the structural guard. -/
theorem ObstructionBudgetSATSearch (G D : Language Bool) (hD : D ∈ P)
    (hsub : ∀ φ ψ : CNF, ψ.Sublist φ → encodeCNF φ ∈ G → encodeCNF ψ ∈ G)
    (hsat : ∀ ψ : CNF, encodeCNF ψ ∈ G → (encodeCNF ψ ∈ D ↔ Satisfiable ψ))
    (a : ℕ) (ha : 0 < a) (select : CNF → List ℕ) (pick : List Bool → List Bool)
    (hpick : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pick)
    (hpickSpec : ∀ φ : CNF, pick (encodeCNF φ) = encodeClause ((select φ).map (fun x => (x,true))))
    (hclear : ∀ φ : CNF, select φ = [] ↔ encodeCNF φ ∈ G)
    (hwidth : ∀ φ : CNF, (select φ).length ≤ a)
    (hhit : ∀ (φ : CNF) (xs : List ℕ), encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G →
      select φ ≠ [] → ∃ x ∈ select φ, x ∈ xs)
    (hshort : ∀ (φ extra : CNF), (∀ c ∈ extra, c.length ≤ 1) → encodeCNF φ ∈ G → encodeCNF (φ ++ extra) ∈ G)
    (q : Polynomial ℕ) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∃ k : ℕ, (2*a)^k ≤ q.eval (encodeCNF φ).length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let C : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    (∃ k : ℕ, (2*a)^k ≤ q.eval x.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
      encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G) ∧ Satisfiable φ}
  have hp : C ∈ P :=
    (ExactObstructionBudgetSAT G D hD hsub hsat a ha select pick hpick hpickSpec hclear hwidth hhit q).2
  obtain ⟨search,hsearch,hr⟩ := SparseVariableSATSearch C hp
  refine ⟨search,hsearch,fun φ hf => hr φ (fun ls => ?_)⟩
  let extra : CNF := ls.map (fun l => [l])
  let ψ := φ ++ extra
  change encodeCNF ψ ∈ C ↔ Satisfiable ψ
  constructor
  · rintro ⟨p,he,_,hs⟩
    exact encodeCNF_injective he ▸ hs
  · intro hs
    obtain ⟨k,hk,xs,hxs,hg⟩ := hf
    have hlen : (encodeCNF φ).length ≤ (encodeCNF ψ).length := by
      simp [ψ,encodeCNF]
    let trim := fun c : Clause => c.filter (fun l => decide (l.1 ∉ xs))
    have hsmall : ∀ c ∈ extra.map trim, c.length ≤ 1 := by
      intro c hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hd
      exact List.length_filter_le _ _
    refine ⟨ψ,rfl,⟨k,hk.trans (Nat.add_le_add_right (eval_mono q hlen) _),xs,hxs,?_⟩,hs⟩
    change encodeCNF (ψ.map trim) ∈ G
    unfold ψ
    rw [List.map_append]
    exact hshort _ _ hsmall hg

end PEqualNP.Outside
