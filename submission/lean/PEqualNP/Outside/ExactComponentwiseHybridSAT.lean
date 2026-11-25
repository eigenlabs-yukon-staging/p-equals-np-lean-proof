import PEqualNP.Outside.ComponentwiseSAT
import PEqualNP.Outside.ExactHornSAT
import PEqualNP.Outside.ExactPolynomialBudgetTwoSATBackdoor
import PEqualNP.Library.L047

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

def hybridShape (q : Polynomial ℕ) (p : CNF) : Prop :=
  (∀ c ∈ p, (c.filter (fun l => l.2)).length ≤ 1) ∨
  (∃ k : ℕ, 6^k ≤ q.eval (encodeCNF p).length + 1 ∧
    ∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2 (p.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))))

/-- Each independently connected part can use either Horn SAT or the
polynomial-rank 2-CNF variable-deletion solver. -/
theorem ExactComponentwiseHybridSAT (q : Polynomial ℕ) :
    let part := fun (φ : CNF) (x : ℕ) => φ.filter (fun c =>
      @decide (∃ m ∈ c, Relation.ReflTransGen (fun a b : ℕ =>
        ∃ d ∈ φ, a ∈ d.map Prod.fst ∧ b ∈ d.map Prod.fst) x m.1) (Classical.propDecidable _))
    {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧ (∀ c ∈ φ, ∀ l ∈ c,
      let p := part φ l.1
      (∀ d ∈ p, (d.filter (fun m => m.2)).length ≤ 1) ∨
      (∃ k : ℕ, 6^k ≤ q.eval (encodeCNF p).length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (p.map (fun d => d.filter (fun m => decide (m.1 ∉ xs)))))) ∧ Satisfiable φ} ∈ P := by
  let A : CNF → Prop := fun p => ∀ c ∈ p, (c.filter (fun l => l.2)).length ≤ 1
  let B : CNF → Prop := fun p => ∃ k : ℕ, 6^k ≤ q.eval (encodeCNF p).length + 1 ∧
    ∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2 (p.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))
  let GA : Language Bool := {s | ∃ p, encodeCNF p = s ∧ A p}
  let GB : Language Bool := {s | ∃ p, encodeCNF p = s ∧ B p}
  let DA : Language Bool := {s | ∃ p, encodeCNF p = s ∧ A p ∧ Satisfiable p}
  let DB : Language Bool := {s | ∃ p, encodeCNF p = s ∧ B p ∧ Satisfiable p}
  let G := GA ⊔ GB
  let D := DA ⊔ DB
  have gA : GA ∈ P := MeasuredHornGuard
  have gB : GB ∈ P := by
    have he : GB = {s | ∃ p : CNF, encodeCNF p = s ∧
      ∃ k : ℕ, 6^k ≤ q.eval s.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (p.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))} := by
      ext s
      constructor
      · rintro ⟨p,rfl,hs⟩
        exact ⟨p,rfl,hs⟩
      · rintro ⟨p,rfl,hs⟩
        exact ⟨p,rfl,hs⟩
    rw [he]
    exact (ExactPolynomialBudgetTwoSATBackdoor q).1
  have dA : DA ∈ P := ExactHornSAT
  have dB : DB ∈ P := by
    have he : DB = {s | ∃ p : CNF, encodeCNF p = s ∧
      (∃ k : ℕ, 6^k ≤ q.eval s.length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (p.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧ Satisfiable p} := by
      ext s
      constructor
      · rintro ⟨p,rfl,hs⟩
        exact ⟨p,rfl,hs⟩
      · rintro ⟨p,rfl,hs⟩
        exact ⟨p,rfl,hs⟩
    rw [he]
    exact (ExactPolynomialBudgetTwoSATBackdoor q).2
  have hG : G ∈ P := L047 GA GB gA gB
  have hD : D ∈ P := L047 DA DB dA dB
  have hguard (p : CNF) : encodeCNF p ∈ G ↔ A p ∨ B p := by
    change ((∃ f, encodeCNF f = encodeCNF p ∧ A f) ∨ (∃ f, encodeCNF f = encodeCNF p ∧ B f)) ↔ _
    constructor
    · rintro (⟨f,hf,ha⟩ | ⟨f,hf,hb⟩)
      · exact Or.inl (encodeCNF_injective hf ▸ ha)
      · exact Or.inr (encodeCNF_injective hf ▸ hb)
    · rintro (ha | hb)
      · exact Or.inl ⟨p,rfl,ha⟩
      · exact Or.inr ⟨p,rfl,hb⟩
  have hspec (p : CNF) (hg : encodeCNF p ∈ G) : encodeCNF p ∈ D ↔ Satisfiable p := by
    change ((∃ f, encodeCNF f = encodeCNF p ∧ A f ∧ Satisfiable f) ∨
      (∃ f, encodeCNF f = encodeCNF p ∧ B f ∧ Satisfiable f)) ↔ _
    constructor
    · rintro (⟨f,hf,_,hs⟩ | ⟨f,hf,_,hs⟩)
      · exact encodeCNF_injective hf ▸ hs
      · exact encodeCNF_injective hf ▸ hs
    · intro hs
      rcases (hguard p).mp hg with ha | hb
      · exact Or.inl ⟨p,rfl,ha,hs⟩
      · exact Or.inr ⟨p,rfl,hb,hs⟩
  have h := ComponentwiseSAT G D hG hD hspec
  change {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧
    (∀ c ∈ φ, ∀ l ∈ c, A (component φ l.1) ∨ B (component φ l.1)) ∧ Satisfiable φ} ∈ P
  change {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧
    (∀ c ∈ φ, ∀ l ∈ c, encodeCNF (component φ l.1) ∈ G) ∧ Satisfiable φ} ∈ P at h
  simpa only [hguard] using h

end PEqualNP.Outside
