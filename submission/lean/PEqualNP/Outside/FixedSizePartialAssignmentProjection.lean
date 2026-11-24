import PEqualNP.Outside.FixedBackdoorProjectComplete
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Outside.PartialAssignmentFacts
import PEqualNP.Library.Universal.Padding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.FixedBackdoorProjectCore (query query_cpt)
open PEqualNP.Outside.FixedBackdoorProjectSemantics (digits query_repr)
open PEqualNP.Outside.FixedBackdoorProjectComplete (query_complete)
open PEqualNP.Outside.AllFormulaNames (distinct distinct_length mem_distinct)
open PEqualNP.Outside.CnfRestrictionSemantics (valueOf)
open PEqualNP.Outside.PartialAssignmentFacts (valueOf_filter assignment)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

private theorem wfFlag_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem size_pow_le (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  cases e : n.size with
  | zero => simp; omega
  | succ d =>
    have hd : d < n.size := by omega
    have h := Nat.lt_size.mp hd
    rw [pow_succ, Nat.mul_comm]
    omega

theorem PEqualNP.Outside.FixedSizePartialAssignmentProjection
    (H : Language Bool) (hH : H ∈ P) (k : ℕ) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ x, x ∈ L ↔ ∃ φ : CNF, encodeCNF φ = x ∧
        ∃ (a : List ℕ) (σ : Assignment), a.length ≤ k ∧
          (∀ i ∈ a, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i) ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           encodeCNF (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone)) ∈ H) := by
  obtain ⟨dec, hd, htime⟩ := hH
  let p : Polynomial ℕ := (Polynomial.C 4 * (Polynomial.X + 1)) ^ k
  let R : Set (List Bool × List Bool) := {q | query k q ∈ H}
  let test : List Bool × List Bool → Bool := fun q => dec (query k q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hd (query k q)
  have ttime : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp (query_cpt k) htime
  obtain ⟨select, hselect, hfind⟩ :=
    EnumeratingSelector.select_bounded R p (Polynomial.C 2 * p) ⟨test, htest, ttime⟩
  let answer (x : List Bool) :=
    (sel (bflag (wfB x)) [true] (sel (bflag (test (x, select x))) [true] [])).isEmpty
  let L : Language Bool := {x | answer x = true}
  have htimeL : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool answer := by
    have ht := cpt_bitFlag (cpt_comp (cpt_pair cpt_id hselect) ttime)
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const [true])
      (cpt_sel ht (cpt_const [true]) (cpt_const []))) cpt_isEmpty
    exact h
  have ha (x : List Bool) : x ∈ L ↔ wfB x = true ∧ test (x, select x) = true := by
    change answer x = true ↔ _
    cases h : wfB x <;> cases ht : test (x, select x) <;> simp [answer, h, ht, bflag, sel]
  refine ⟨L, ⟨answer, fun _ => Iff.rfl, htimeL⟩, ?_⟩
  intro x
  constructor
  · intro h
    obtain ⟨hw, hp⟩ := (ha x).mp h
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp hw
    obtain ⟨a, v, hlen, hm, he⟩ := query_repr k φ (select (encodeCNF φ))
    have hmem := (htest _).mpr hp
    change query k _ ∈ H at hmem
    rw [he] at hmem
    refine ⟨φ, rfl, a, fun i => decide (i ∈ v), hlen, fun i hi => (mem_distinct φ i).mp (hm i hi), ?_⟩
    change encodeCNF (restrict (fun i => if i ∈ a then some (decide (i ∈ v)) else none) φ) ∈ H
    have heq : valueOf a v = (fun i => if i ∈ a then some (decide (i ∈ v)) else none) := by
      funext i
      by_cases hi : i ∈ a <;> by_cases hv : i ∈ v <;> simp [valueOf, hi, hv]
    rwa [← heq]
  · rintro ⟨φ, rfl, a, σ, hlen, hm, hs⟩
    let x := encodeCNF φ
    obtain ⟨word, hword, he⟩ := query_complete k φ a σ hlen (fun i hi => (mem_distinct φ i).mpr (hm i hi))
    have hmem : query k (x, word) ∈ H := by
      rw [he, valueOf_filter]
      have hrho : assignment a.toFinset σ = (fun i => if i ∈ a then some (σ i) else none) := by
        funext i
        simp only [assignment, List.mem_toFinset]
      rwa [hrho]
    have hbase : 2 ^ (digits φ + 1) ≤ 4 * (x.length + 1) := by
      unfold digits
      rw [pow_succ]
      have h₁ := size_pow_le ((distinct φ).length - 1)
      have h₂ := distinct_length φ
      change (distinct φ).length ≤ x.length at h₂
      omega
    have hpow : 2 ^ word.length ≤ p.eval x.length := by
      refine (Nat.pow_le_pow_right (by decide) hword).trans ?_
      rw [pow_mul]
      simp only [p, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      exact Nat.pow_le_pow_left hbase _
    have hl : word.length ≤ p.eval x.length := Nat.lt_two_pow_self.le.trans hpow
    have hbudget : 2 ^ (word.length + 1) ≤ (Polynomial.C 2 * p).eval x.length := by
      rw [pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hpow
    have hidx := (BoundedEnumeration.idx_bound word).trans hbudget
    exact (ha _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩,
      (htest _).mp (hfind x ⟨word, ⟨hl, hmem⟩, (Nat.le_add_right _ _).trans hidx⟩).2⟩
