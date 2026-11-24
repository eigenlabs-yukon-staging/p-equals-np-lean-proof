import PEqualNP.Outside.PolynomialBudgetPartialAssignmentProjection
import PEqualNP.Library.L008

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside (PolynomialBudgetPartialAssignmentProjection)

private def admissible (p : Polynomial ℕ) (φ : CNF) (a : List ℕ) : Prop :=
  let m := (φ.flatMap fun c => c.map Prod.fst).toFinset.card
  2 ^ (((m - 1).size + 1) * a.length) ≤ p.eval (encodeCNF φ).length ∧
    ∀ i ∈ a, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i

private def gameResidual (φ : CNF) (a : List ℕ) (σ : Assignment) : CNF :=
  let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
  φ.filterMap fun c =>
    if c.any (fun l => ρ l.1 == some l.2) then none
    else some (c.filter fun l => (ρ l.1).isNone)

private def layer (q : Bool × Polynomial ℕ) (next : CNF → Prop) (φ : CNF) : Prop :=
  if q.1 then ∀ a : List ℕ, ∀ σ : Assignment, admissible q.2 φ a → next (gameResidual φ a σ)
  else ∃ (a : List ℕ) (σ : Assignment), admissible q.2 φ a ∧ next (gameResidual φ a σ)

private theorem fold_decider (H : Language Bool) (hH : H ∈ P)
    (stages : List (Bool × Polynomial ℕ)) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ φ : CNF, encodeCNF φ ∈ L ↔ stages.foldr layer (fun ψ => encodeCNF ψ ∈ H) φ := by
  induction stages with
  | nil => exact ⟨H, hH, fun _ => Iff.rfl⟩
  | cons q qs ih =>
    obtain ⟨M, hM, hs⟩ := ih
    cases hq : q.1
    · obtain ⟨L, hL, hp⟩ := PolynomialBudgetPartialAssignmentProjection M hM q.2
      refine ⟨L, hL, ?_⟩
      intro φ
      change encodeCNF φ ∈ L ↔ layer q (qs.foldr layer (fun ψ => encodeCNF ψ ∈ H)) φ
      have he : encodeCNF φ ∈ L ↔
          ∃ (a : List ℕ) (σ : Assignment), admissible q.2 φ a ∧ encodeCNF (gameResidual φ a σ) ∈ M := by
        refine (hp _).trans ?_
        constructor
        · rintro ⟨ψ, h, a, σ, hb, hv, hm⟩
          obtain rfl := PEqualNP.Library.SearchHelpers.encodeCNF_injective h
          exact ⟨a, σ, ⟨hb, hv⟩, hm⟩
        · rintro ⟨a, σ, ⟨hb, hv⟩, hm⟩
          exact ⟨φ, rfl, a, σ, hb, hv, hm⟩
      rw [he, layer, hq]
      simp only [Bool.false_eq_true, ite_false]
      exact exists_congr (fun a => exists_congr (fun σ => and_congr_right (fun _ => hs _)))
    · obtain ⟨L, hL, hp⟩ := PolynomialBudgetPartialAssignmentProjection Mᶜ (L008 M hM) q.2
      refine ⟨Lᶜ, L008 L hL, ?_⟩
      intro φ
      change encodeCNF φ ∉ L ↔ layer q (qs.foldr layer (fun ψ => encodeCNF ψ ∈ H)) φ
      have he : encodeCNF φ ∈ L ↔
          ∃ (a : List ℕ) (σ : Assignment), admissible q.2 φ a ∧ encodeCNF (gameResidual φ a σ) ∉ M := by
        refine (hp _).trans ?_
        constructor
        · rintro ⟨ψ, h, a, σ, hb, hv, hm⟩
          obtain rfl := PEqualNP.Library.SearchHelpers.encodeCNF_injective h
          exact ⟨a, σ, ⟨hb, hv⟩, hm⟩
        · rintro ⟨a, σ, ⟨hb, hv⟩, hm⟩
          exact ⟨φ, rfl, a, σ, hb, hv, hm⟩
      rw [he, layer, hq]
      simp only [ite_true]
      constructor
      · intro h a σ ha
        apply (hs _).mp
        by_contra hm
        exact h ⟨a, σ, ha, hm⟩
      · intro h
        rintro ⟨a, σ, ha, hm⟩
        exact hm ((hs _).mpr (h a σ ha))

theorem PEqualNP.Outside.FiniteAlternatingPartialAssignmentProjection
    (H : Language Bool) (hH : H ∈ P) (stages : List (Bool × Polynomial ℕ)) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ φ : CNF, encodeCNF φ ∈ L ↔
        stages.foldr (fun q next ψ =>
          let admissible := fun a : List ℕ =>
            let m := (ψ.flatMap fun c => c.map Prod.fst).toFinset.card
            2 ^ (((m - 1).size + 1) * a.length) ≤ q.2.eval (encodeCNF ψ).length ∧
              ∀ i ∈ a, ∃ c ∈ ψ, ∃ l ∈ c, l.1 = i
          let res := fun (a : List ℕ) (σ : Assignment) =>
            let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
            ψ.filterMap fun c =>
              if c.any (fun l => ρ l.1 == some l.2) then none
              else some (c.filter fun l => (ρ l.1).isNone)
          if q.1 then ∀ a : List ℕ, ∀ σ : Assignment, admissible a → next (res a σ)
          else ∃ (a : List ℕ) (σ : Assignment), admissible a ∧ next (res a σ))
          (fun ψ => encodeCNF ψ ∈ H) φ :=
  fold_decider H hH stages
