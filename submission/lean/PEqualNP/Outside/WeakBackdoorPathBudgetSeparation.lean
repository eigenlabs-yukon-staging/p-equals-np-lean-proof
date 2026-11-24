import PEqualNP.Outside.SmallWeakBackdoorPathBudgetSATInP

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.RestrictCnfHelpers (restrict)
open PEqualNP.Outside.PartialAssignmentFacts (assignment)
open PEqualNP.Outside.FirstWideClause (firstWide)

local notation "frontClause" => ([(0, true), (1, false), (1, false)] : Clause)
local notation "endClause" => ([(1, true), (1, true), (1, true)] : Clause)
local notation "middleClause" n => (List.replicate n (0, true) : Clause)

theorem PEqualNP.Outside.WeakBackdoorPathBudgetSeparation :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ n : ℕ, 5 ≤ n →
        let φ : CNF :=
          [[(0, true), (1, false), (1, false)], List.replicate n (0, true),
            [(1, true), (1, true), (1, true)]]
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
          2 ^ (((w - 1).size + 1) * a.card) ≤ 64 := by
  obtain ⟨L, hp, hsound, hcomplete⟩ := SmallWeakBackdoorPathBudgetSATInP (Polynomial.C 64)
  refine ⟨L, hp, hsound, ?_⟩
  intro n hn
  let φ : CNF := [frontClause, middleClause n, endClause]
  change encodeCNF φ ∈ L ∧ _
  have hn0 : n ≠ 0 := by omega
  have hn2 : 2 < n := by omega
  constructor
  · apply hcomplete
    let path : List (Clause × Literal) := [(frontClause, (0, true)), (endClause, (1, true))]
    let σ : Assignment := fun _ => true
    refine ⟨σ, path, ?_, ?_, ?_, ?_⟩
    · simp [φ, σ, CNF.eval, Clause.eval, Literal.eval, hn0]
    · intro i v hi
      have hidx := List.getElem?_eq_some_iff.mp hi
      have hlt : i < 2 := by simpa [path] using hidx.choose
      interval_cases i
      · have hv : v = (frontClause, (0, true)) := by simpa [path] using hi.symm
        subst v
        simp [path, φ]
      · have hv : v = (endClause, (1, true)) := by simpa [path] using hi.symm
        subst v
        simp [path, φ, σ, hn0]
    · simp [path, φ, σ, hn0, IsKCNF]
    · norm_num [path] <;> decide
  · rintro ⟨a, σ, w, hsat, hweak, hw, hbudget⟩
    change IsKCNF 2 (restrict (assignment a σ) φ) at hweak
    have hone : 1 ∈ a := by
      by_contra hl
      have hm : endClause ∈ restrict (assignment a σ) φ := by
        simp [φ, restrict, assignment, hl]
      simpa using hweak endClause hm
    have hzero : 0 ∈ a := by
      by_contra hl
      have hm : (middleClause n) ∈ restrict (assignment a σ) φ := by
        simp [φ, restrict, assignment, hl]
      have ht := hweak (middleClause n) hm
      simp at ht
      omega
    have htrue : σ 1 = true := by
      simpa [φ, CNF.eval, Clause.eval, Literal.eval] using (List.all_eq_true.mp hsat endClause (by simp [φ]))
    have htwo : 2 ≤ a.card := by
      have hs : ({0, 1} : Finset ℕ) ⊆ a := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hzero
        · exact hone
      simpa using Finset.card_le_card hs
    have hfirst : firstWide (restrict (assignment {1} σ) φ) = some (middleClause n) := by
      simp [firstWide, restrict, assignment, φ, htrue, hn2]
    have hlen := hw {1} (Finset.singleton_subset_iff.mpr hone) (middleClause n) hfirst
    simp at hlen
    have hd : 2 < (w - 1).size := Nat.lt_size.mpr (by omega)
    have hexp : 8 ≤ ((w - 1).size + 1) * a.card := by
      exact Nat.mul_le_mul (show 4 ≤ (w - 1).size + 1 by omega) htwo
    have hp' : 256 ≤ 2 ^ (((w - 1).size + 1) * a.card) :=
      Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) hexp
    omega
