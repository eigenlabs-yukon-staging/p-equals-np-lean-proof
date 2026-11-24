import PEqualNP.Outside.SmallWeakBackdoorShortestWidthSATInP

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.RestrictCnfHelpers (restrict)
open PEqualNP.Outside.PartialAssignmentFacts (assignment)
open PEqualNP.Outside.FirstWideClause (firstWide)

theorem PEqualNP.Outside.ShortestWidthBudgetSeparation :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ n : ℕ, 4 ≤ n →
        let φ : CNF :=
          [(0, true) :: (List.range n).map (fun i => (i + 3, false)),
            [(0, true), (1, false), (2, false)]]
        encodeCNF φ ∈ L ∧
        ¬ ∃ (a : Finset ℕ) (σ : Assignment) (w : ℕ),
          CNF.eval σ φ = true ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           IsKCNF 2 (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone))) ∧
          (∀ b ⊆ a, ∀ c,
            (let ρ := fun i : ℕ => if i ∈ b then some (σ i) else none
             ((show CNF from φ.filterMap fun d =>
               if d.any (fun l => ρ l.1 == some l.2) then none
               else some (d.filter fun l => (ρ l.1).isNone))).find?
                 (fun d => decide (2 < d.length))) = some c → c.length ≤ w) ∧
          2 ^ (((w - 1).size + 1) * a.card) ≤ 8 := by
  obtain ⟨L, hp, hsound, hcomplete⟩ := SmallWeakBackdoorShortestWidthSATInP (Polynomial.C 8)
  refine ⟨L, hp, hsound, ?_⟩
  intro n hn
  let short : Clause := [(0, true), (1, false), (2, false)]
  let long : Clause := (0, true) :: (List.range n).map (fun i => (i + 3, false))
  let φ : CNF := [long, short]
  change encodeCNF φ ∈ L ∧ _
  let a : Finset ℕ := {0}
  let σ : Assignment := fun _ => true
  have hsat : CNF.eval σ φ = true := by
    simp [φ, short, long, σ, CNF.eval, Clause.eval, Literal.eval]
  have hnone (τ : Assignment) : restrict (assignment ∅ τ) φ = φ := by
    simp [φ, short, long, restrict, assignment]
  have hfull : restrict (assignment a σ) φ = [] := by
    simp [φ, short, long, restrict, assignment, a, σ]
  constructor
  · apply hcomplete
    refine ⟨a, σ, 3, hsat, ?_, ?_, ?_⟩
    · change IsKCNF 2 (restrict (assignment a σ) φ)
      rw [hfull]
      simp [IsKCNF]
    · intro b hb
      change IsKCNF 2 (restrict (assignment b σ) φ) ∨
        ∃ c ∈ restrict (assignment b σ) φ, 2 < List.length c ∧ List.length c ≤ 3
      rcases Finset.subset_singleton_iff.mp hb with rfl | he
      · rw [hnone]
        exact Or.inr ⟨short, by simp [φ], by decide, by decide⟩
      · rw [show b = a from he, hfull]
        simp [IsKCNF]
    · norm_num [a] <;> decide
  · rintro ⟨b, τ, w, _, hweak, hw, hcost⟩
    change IsKCNF 2 (restrict (assignment b τ) φ) at hweak
    have hb : 1 ≤ b.card := by
      by_contra! hz
      have he : b = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [he, hnone] at hweak
      have hc := hweak short (by simp [φ])
      simp [short] at hc
    have hf : firstWide (restrict (assignment ∅ τ) φ) = some long := by
      rw [hnone]
      have hlong : 2 < n + 1 := by omega
      simp [firstWide, φ, long, Nat.add_comm, hlong]
    have hw' := hw ∅ (Finset.empty_subset b) long hf
    simp [long] at hw'
    have hd : 2 < (w - 1).size := Nat.lt_size.mpr (by omega)
    have he : 4 ≤ ((w - 1).size + 1) * b.card :=
      (show 4 ≤ (w - 1).size + 1 by omega).trans (Nat.le_mul_of_pos_right _ hb)
    have hh : 16 ≤ 2 ^ (((w - 1).size + 1) * b.card) :=
      Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) he
    omega
