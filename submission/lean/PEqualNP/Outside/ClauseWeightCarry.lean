import PEqualNP.Library.SearchHelpers.Weight

namespace PEqualNP.Outside

open PEqualNP.Search

private def mass : List ℕ → ℚ
  | [] => 0
  | h :: t => (h : ℚ) + mass t / 2

private def carry : List ℕ → ℕ
  | [] => 0
  | h :: t => h + carry t / 2

private theorem carry_bounds (xs : List ℕ) :
    (carry xs : ℚ) ≤ mass xs ∧ mass xs < (carry xs : ℚ)+1 := by
  induction xs with
  | nil => norm_num [mass,carry]
  | cons h xs ih =>
      let d := carry xs / 2
      let r := carry xs % 2
      have hr : r < 2 := Nat.mod_lt _ (by decide)
      have he : carry xs = 2*d + r := by
        dsimp [d,r]
        omega
      have hdq : (carry xs : ℚ) = (2 : ℚ)*(d : ℚ)+(r : ℚ) := by exact_mod_cast he
      have hr0 : (0 : ℚ) ≤ (r : ℚ) := by positivity
      have hr1 : (r : ℚ) ≤ 1 := by exact_mod_cast (show r ≤ 1 by omega)
      simp only [carry,mass,Nat.cast_add]
      change (h : ℚ)+(d : ℚ) ≤ _ ∧ _ < (h : ℚ)+(d : ℚ)+1
      constructor
      · linarith [ih.1]
      · linarith [ih.2]

private def bin (φ : CNF) (k : ℕ) : ℕ := (φ.filter (fun c => c.length = k)).length

private def widthMass (φ : CNF) (start n : ℕ) : ℚ :=
  (φ.map (fun c => if start ≤ c.length ∧ c.length < start+n then
    (2 : ℚ)⁻¹ ^ (c.length-start) else 0)).sum

private theorem split_mass (φ : CNF) (start n : ℕ) :
    widthMass φ start (n+1) = (bin φ start : ℚ) + widthMass φ (start+1) n / 2 := by
  induction φ with
  | nil => simp [widthMass,bin]
  | cons c φ ih =>
      simp only [widthMass,List.map_cons,List.sum_cons] at ih ⊢
      unfold bin at ih ⊢
      let t := c.length
      by_cases h : t = start
      · have h0 : start ≤ c.length ∧ c.length < start+(n+1) := by dsimp [t] at h; omega
        have h1 : ¬ (start+1 ≤ c.length ∧ c.length < start+1+n) := by dsimp [t] at h; omega
        have he : c.length = start := h
        simp only [List.filter_cons,he,decide_true,ite_true,List.length_cons,Nat.cast_add,Nat.cast_one,
          h0, h1]
        simp [he] at h0 h1
        simp only [he,Nat.sub_self,pow_zero]
        have hlt : start < start+(n+1) := by omega
        have hn : ¬ start+1 ≤ start := by omega
        simp only [hlt,hn,le_refl,true_and,false_and,if_true,if_false,zero_add]
        linarith only [ih]
      · have htrue (hc : start ≤ c.length ∧ c.length < start+(n+1)) :
            start+1 ≤ c.length ∧ c.length < start+1+n := by
          dsimp [t] at h
          omega
        have hfalse (hc : ¬(start ≤ c.length ∧ c.length < start+(n+1))) :
            ¬(start+1 ≤ c.length ∧ c.length < start+1+n) := by omega
        have h' : c.length ≠ start := h
        simp only [List.filter_cons,h',decide_false,Bool.false_eq_true,ite_false]
        by_cases hc : start ≤ c.length ∧ c.length < start+(n+1)
        · simp only [hc,htrue hc,ite_true]
          have he : c.length-start = (c.length-(start+1))+1 := by
            have := htrue hc
            omega
          simp only [true_and,if_true]
          rw [he,pow_succ]
          ring_nf at ih ⊢
          linarith only [ih]
        · simp only [hc,hfalse hc,ite_false,zero_add]
          exact ih

private theorem histogram_mass (φ : CNF) (start n : ℕ) :
    mass ((List.range' start n).map (bin φ)) = widthMass φ start n := by
  induction n generalizing start with
  | zero =>
      unfold widthMass
      have h (c : Clause) : ¬ (start ≤ c.length ∧ c.length < start) := by omega
      simp [mass,h]
  | succ n ih =>
      change mass (bin φ start :: (List.range' (start+1) n).map (bin φ)) = _
      rw [mass,ih,split_mass]

/-- The clause-weight threshold is equivalent to a descending unary carry calculation. -/
theorem ClauseWeightCarry (φ : CNF) (n : ℕ) (hn : ∀ c ∈ φ, c.length ≤ n) :
    ((List.range (n+1)).map (fun i => (φ.filter (fun c => c.length = i)).length)).foldr
      (fun count next => count + next / 2) 0 = 0 ↔
      (φ.map (fun c => (2 : ℚ)⁻¹ ^ c.length)).sum < 1 := by
  let xs := (List.range (n+1)).map (bin φ)
  have hc : xs.foldr (fun count next => count+next/2) 0 = carry xs := by
    induction xs with
    | nil => rfl
    | cons h t ih => simp [carry,ih]
  have hm : mass xs = (φ.map (fun c => (2 : ℚ)⁻¹ ^ c.length)).sum := by
    dsimp only [xs]
    rw [List.range_eq_range',histogram_mass]
    unfold widthMass
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    have h : 0 ≤ c.length ∧ c.length < 0+(n+1) := by have := hn c hc; omega
    rw [if_pos h,Nat.sub_zero]
  change xs.foldr (fun count next => count+next/2) 0 = 0 ↔ _
  rw [hc,← hm]
  have hb := carry_bounds xs
  constructor
  · intro h
    simpa [h] using hb.2
  · intro h
    by_contra hnz
    have hpos : 1 ≤ carry xs := by omega
    have hq : (1 : ℚ) ≤ (carry xs : ℚ) := by exact_mod_cast hpos
    linarith [hb.1]

end PEqualNP.Outside
