import PEqualNP.Outside.BudgetBackdoorProjectSemantics
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Outside.PartialAssignmentFacts
import PEqualNP.Library.Universal.Padding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.BudgetBackdoorProjectCore (query query_cpt unaryBudget unaryBudget_cpt)
open PEqualNP.Outside.FixedBackdoorProjectSemantics (digits)
open PEqualNP.Outside.BudgetBackdoorProjectSemantics (query_complete query_repr)
open PEqualNP.Outside.AllFormulaNames (distinct vars mem_distinct)
open PEqualNP.Outside.CnfRestrictionSemantics (valueOf)
open PEqualNP.Outside.PartialAssignmentFacts (valueOf_filter assignment)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

private theorem wfFlag_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem digits_eq (φ : CNF) :
    digits φ = ((φ.flatMap fun c => c.map Prod.fst).toFinset.card - 1).size := by
  unfold digits distinct
  rw [PEqualNP.Outside.UniqueNameScan.scan_count]
  rfl

theorem PEqualNP.Outside.PolynomialBudgetPartialAssignmentProjection
    (H : Language Bool) (hH : H ∈ P) (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ x, x ∈ L ↔ ∃ φ : CNF, encodeCNF φ = x ∧
        ∃ (a : List ℕ) (σ : Assignment),
          (let n := (φ.flatMap fun c => c.map Prod.fst).toFinset.card
           2 ^ (((n - 1).size + 1) * a.length) ≤ p.eval x.length) ∧
          (∀ i ∈ a, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i) ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           encodeCNF (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone)) ∈ H) := by
  obtain ⟨dec, hd, htime⟩ := hH
  let R : Set (List Bool × List Bool) := {q | query p q ∈ H}
  let test : List Bool × List Bool → Bool := fun q => dec (query p q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hd (query p q)
  have ttime : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp (query_cpt p) htime
  obtain ⟨select, hselect, hfind⟩ :=
    EnumeratingSelector.select_bounded R p (Polynomial.C 2 * p) ⟨test, htest, ttime⟩
  let answer (x : List Bool) :=
    (sel (bflag (wfB x)) [true] (sel (unaryBudget p x) [true]
      (sel (bflag (test (x, select x))) [true] []))).isEmpty
  let L : Language Bool := {x | answer x = true}
  have htimeL : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool answer := by
    have ht := cpt_bitFlag (cpt_comp (cpt_pair cpt_id hselect) ttime)
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const [true])
      (cpt_sel (unaryBudget_cpt p) (cpt_const [true])
        (cpt_sel ht (cpt_const [true]) (cpt_const [])))) cpt_isEmpty
    exact h
  have ha (x : List Bool) : x ∈ L ↔ wfB x = true ∧ 0 < p.eval x.length ∧ test (x, select x) = true := by
    change answer x = true ↔ _
    by_cases hb : p.eval x.length = 0 <;> cases h : wfB x <;> cases ht : test (x, select x) <;>
      simp [answer, h, ht, bflag, sel, unaryBudget, un, hb, Nat.pos_iff_ne_zero]
  refine ⟨L, ⟨answer, fun _ => Iff.rfl, htimeL⟩, ?_⟩
  intro x
  constructor
  · intro h
    obtain ⟨hw, hpos, hp⟩ := (ha x).mp h
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp hw
    obtain ⟨a, v, hlen, hm, he⟩ := query_repr p φ (select (encodeCNF φ)) hpos
    have hmem := (htest _).mpr hp
    change query p _ ∈ H at hmem
    rw [he] at hmem
    refine ⟨φ, rfl, a, fun i => decide (i ∈ v), by simpa only [digits_eq] using hlen, fun i hi => (mem_distinct φ i).mp (hm i hi), ?_⟩
    change encodeCNF (restrict (fun i => if i ∈ a then some (decide (i ∈ v)) else none) φ) ∈ H
    have heq : valueOf a v = (fun i => if i ∈ a then some (decide (i ∈ v)) else none) := by
      funext i
      by_cases hi : i ∈ a <;> by_cases hv : i ∈ v <;> simp [valueOf, hi, hv]
    rwa [← heq]
  · rintro ⟨φ, rfl, a, σ, hlen, hm, hs⟩
    let x := encodeCNF φ
    obtain ⟨word, hword, he⟩ := query_complete p φ a σ (by simpa only [digits_eq] using hlen) (fun i hi => (mem_distinct φ i).mpr (hm i hi))
    have hmem : query p (x, word) ∈ H := by
      rw [he, valueOf_filter]
      have hrho : assignment a.toFinset σ = (fun i => if i ∈ a then some (σ i) else none) := by
        funext i
        simp only [assignment, List.mem_toFinset]
      rwa [hrho]
    have hpow : 2 ^ word.length ≤ p.eval x.length := hword
    have hpos : 0 < p.eval x.length := (Nat.two_pow_pos _).trans_le hpow
    have hl : word.length ≤ p.eval x.length := Nat.lt_two_pow_self.le.trans hpow
    have hbudget : 2 ^ (word.length + 1) ≤ (Polynomial.C 2 * p).eval x.length := by
      rw [pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hpow
    have hidx := (BoundedEnumeration.idx_bound word).trans hbudget
    exact (ha _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, hpos,
      (htest _).mp (hfind x ⟨word, ⟨hl, hmem⟩, (Nat.le_add_right _ _).trans hidx⟩).2⟩
