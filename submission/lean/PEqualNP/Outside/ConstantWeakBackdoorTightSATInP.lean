import PEqualNP.Outside.SmallWeakBackdoorWidthBudgetSATInP

open PEqualNP.Search PEqualNP.Library
open PEqualNP.Outside.MaxClauseWidthMachine (maxWidth)
open PEqualNP.Outside.WidthDigitClock (maxWidth_fold)

private theorem width_le_encoded (φ : CNF) : IsKCNF (encodeCNF φ).length φ := by
  intro c hc
  have h₁ := PEqualNP.Library.SearchHelpers.SatV.length_le_flatMap_lit c
  have h₂ : (c.flatMap encodeLiteral).length ≤ (encodeCNF φ).length := by
    induction φ with
    | nil => simp at hc
    | cons a φ ih =>
      simp only [encodeCNF, List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp hc with rfl | h
      · simp [encodeClause]
        omega
      · have he := ih h
        unfold encodeCNF at he
        omega
  exact h₁.trans h₂

private theorem size_pow_le (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  cases e : n.size with
  | zero => simp; omega
  | succ d =>
    have hd : d < n.size := by omega
    have h := Nat.lt_size.mp hd
    rw [pow_succ, Nat.mul_comm]
    omega

theorem PEqualNP.Outside.ConstantWeakBackdoorTightSATInP (k : ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF,
        (∃ (a : Finset ℕ) (σ : Assignment), a.card ≤ k ∧ CNF.eval σ φ = true ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           IsKCNF 2 (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone)))) →
        encodeCNF φ ∈ L := by
  let p : Polynomial ℕ := (Polynomial.C 4 * (Polynomial.X + 1)) ^ k
  obtain ⟨L, hp, hs, hc⟩ := SmallWeakBackdoorWidthBudgetSATInP p
  refine ⟨L, hp, hs, ?_⟩
  rintro φ ⟨a, σ, hcard, hsat, hweak⟩
  let n := (encodeCNF φ).length
  refine hc φ ⟨a, σ, hsat, hweak, ?_⟩
  rw [← maxWidth_fold]
  have width_bound (ψ : CNF) (h : IsKCNF n ψ) : maxWidth ψ ≤ n := by
    induction ψ with
    | nil => simp [maxWidth]
    | cons c ψ ih =>
      exact max_le (h c (by simp)) (ih (fun d hd => h d (by simp [hd])))
  have hw := width_bound φ (width_le_encoded φ)
  have hbase : 2 ^ ((maxWidth φ - 1).size + 1) ≤ 4 * (n + 1) := by
    rw [pow_succ]
    have hh := size_pow_le (maxWidth φ - 1)
    omega
  simp only [p, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [pow_mul]
  refine (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right ?_ hcard)
  positivity
