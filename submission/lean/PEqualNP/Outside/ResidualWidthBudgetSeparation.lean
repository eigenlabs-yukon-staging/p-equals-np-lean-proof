import PEqualNP.Outside.SmallWeakBackdoorResidualWidthSATInP

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.RestrictCnfHelpers (restrict)
open PEqualNP.Outside.PartialAssignmentFacts (assignment)
open PEqualNP.Outside.FirstWideClause (firstWide)

theorem PEqualNP.Outside.ResidualWidthBudgetSeparation :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ n : ℕ, 4 ≤ n →
        let φ : CNF :=
          [[(0, true), (1, false), (2, false)],
            (0, true) :: (List.range n).map (fun i => (i + 3, false))]
        encodeCNF φ ∈ L ∧
        ¬ ∃ (a : Finset ℕ) (σ : Assignment),
          CNF.eval σ φ = true ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           IsKCNF 2 (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone))) ∧
          (let w := φ.foldr (fun c t => max c.length t) 0
           2 ^ (((w - 1).size + 1) * a.card) ≤ 8) := by
  obtain ⟨L, hp, hsound, hcomplete⟩ := SmallWeakBackdoorResidualWidthSATInP (Polynomial.C 8)
  refine ⟨L, hp, hsound, ?_⟩
  intro n hn
  let short : Clause := [(0, true), (1, false), (2, false)]
  let long : Clause := (0, true) :: (List.range n).map (fun i => (i + 3, false))
  let φ : CNF := [short, long]
  change encodeCNF φ ∈ L ∧ _
  let a : Finset ℕ := {0}
  let σ : Assignment := fun _ => true
  have hsat : CNF.eval σ φ = true := by
    simp [φ, short, long, σ, CNF.eval, Clause.eval, Literal.eval]
  have hnone (τ : Assignment) : restrict (assignment ∅ τ) φ = φ := by
    simp [φ, short, long, restrict, assignment, List.filter_eq_self]
  have hfull : restrict (assignment a σ) φ = [] := by
    simp [φ, short, long, restrict, assignment, a, σ]
  constructor
  · apply hcomplete
    refine ⟨a, σ, 3, hsat, ?_, ?_, ?_⟩
    · change IsKCNF 2 (restrict (assignment a σ) φ)
      rw [hfull]
      simp [IsKCNF]
    · intro b hb c hc
      change firstWide (restrict (assignment b σ) φ) = some c at hc
      rcases Finset.subset_singleton_iff.mp hb with rfl | he
      · rw [hnone] at hc
        have hh : firstWide φ = some short := by simp [firstWide, φ, short]
        rw [hh] at hc
        obtain rfl := Option.some.inj hc
        decide
      · rw [show b = a from he, hfull] at hc
        simp [firstWide] at hc
    · norm_num [a] <;> decide
  · rintro ⟨b, τ, _, hweak, hcost⟩
    change IsKCNF 2 (restrict (assignment b τ) φ) at hweak
    have hb : 1 ≤ b.card := by
      by_contra! hz
      have he : b = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [he, hnone] at hweak
      have hc := hweak short (by simp [φ])
      simp [short] at hc
    have hw : φ.foldr (fun c t => max c.length t) 0 = n + 1 := by
      simp [φ, short, long, Nat.max_eq_right (show 3 ≤ n + 1 by omega), Nat.add_comm]
    rw [hw] at hcost
    dsimp only at hcost
    rw [Nat.add_sub_cancel] at hcost
    have hd : 2 < n.size := Nat.lt_size.mpr hn
    have he : 4 ≤ (n.size + 1) * b.card := by
      exact (show 4 ≤ n.size + 1 by omega).trans (Nat.le_mul_of_pos_right _ hb)
    have hh : 16 ≤ 2 ^ ((n.size + 1) * b.card) := Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) he
    omega
