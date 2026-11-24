import PEqualNP.Outside.PolynomialBudgetPartialAssignmentProjection
import PEqualNP.Outside.MinimalRankSelector
import PEqualNP.Outside.TrueNamesAsUnits
import Mathlib.Data.List.Dedup

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search
open PEqualNP.Outside.BackdoorPathCore (Word pack cut cut_eq selected setTrue finish)
open PEqualNP.Outside.BudgetBackdoorProjectCore (cap cap_length step endState endState_cpt query query_cpt)
open PEqualNP.Outside.BudgetBackdoorProjectSemantics (query_complete iter_valid)
open PEqualNP.Outside.FixedBackdoorProjectSemantics (digits finish_enc)
open PEqualNP.Outside.AllFormulaNames (vars distinct mem_distinct)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.PartialAssignmentFacts (assignment valueOf_filter)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)
open PEqualNP.Outside.TrueNamesAsUnits (emit emit_cpt emit_enc unitCNF)
open PEqualNP.Outside.MinimalRankSelector (select_least length_le_of_idx_le)

private def budgetCost (φ : CNF) (a : List ℕ) : ℕ :=
  let m := (φ.flatMap fun c => c.map Prod.fst).toFinset.card
  ((m - 1).size + 1) * a.length

private def admittedNames (φ : CNF) (a : List ℕ) : Prop :=
  ∀ i ∈ a, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i

private def restrictTo (φ : CNF) (a : List ℕ) (σ : Assignment) : CNF :=
  restrict (fun i => if i ∈ a then some (σ i) else none) φ

private def accepted (H : Language Bool) (p : Polynomial ℕ) (φ : CNF)
    (a : List ℕ) (σ : Assignment) : Prop :=
  2 ^ budgetCost φ a ≤ p.eval (encodeCNF φ).length ∧ admittedNames φ a ∧
    encodeCNF (restrictTo φ a σ) ∈ H

private def emitted (z : Word) : Word := pairB (emit (selected z)) (emit (setTrue z))

private theorem emitted_cpt :
    ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) emitted := by
  have hs := cpt_comp (cpt_unpairB1_1 cpt_unpairB2) emit_cpt
  have ht := cpt_comp (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)) emit_cpt
  exact cpt_pairB2 hs ht

private theorem digits_cost (φ : CNF) (a : List ℕ) :
    budgetCost φ a = (digits φ + 1) * a.length := by
  unfold budgetCost digits distinct
  rw [PEqualNP.Outside.UniqueNameScan.scan_count]
  rfl

private theorem encode_candidate (H : Language Bool) (p : Polynomial ℕ) (φ : CNF)
    (a : List ℕ) (σ : Assignment) (h : accepted H p φ a σ) :
    ∃ w : Word, w.length ≤ budgetCost φ a ∧
      2 ^ w.length ≤ p.eval (encodeCNF φ).length ∧ query p (encodeCNF φ, w) ∈ H := by
  obtain ⟨hb, hv, ha⟩ := h
  have hv' (i) (hi : i ∈ a) := (mem_distinct φ i).mpr (hv i hi)
  -- A code of exactly the prescribed length is exhibited by the path construction.
  obtain ⟨v, hvlen, hpath⟩ := PEqualNP.Outside.BudgetBackdoorProjectSemantics.path φ [] a σ hv'
  have hlen : v.length = budgetCost φ a := by simpa [digits_cost] using hvlen
  have hvpow : 2 ^ v.length ≤ p.eval (encodeCNF φ).length := hlen ▸ hb
  refine ⟨v, hlen.le, hvpow, ?_⟩
  let x := encodeCNF φ
  change 2 ^ v.length ≤ p.eval x.length at hvpow
  have hcut : cut (cap p x) v = v := by
    rw [cut_eq, cap_length]
    exact List.take_of_length_le (by have ht := Nat.lt_size.mpr hvpow; omega)
  have hn : a.length ≤ v.length := by
    rw [hvlen, Nat.add_mul]
    simp
  have hend : endState p (x, v) =
      pack x (names a) (names (a.filter σ)) [] := by
    change step^[v.length] (pack x [] [] (cut (cap p x) v)) = _
    simp only [List.nil_append, List.filter_nil, names, List.flatMap_nil] at hpath
    rw [hcut, ← Nat.sub_add_cancel hn, Function.iterate_add_apply, hpath]
    exact Function.iterate_fixed
      (PEqualNP.Outside.BudgetBackdoorProjectSemantics.step_short φ a (a.filter σ) [] (by simp)) _
  unfold query
  rw [hend, finish_enc, valueOf_filter]
  have he : assignment a.toFinset σ = (fun i => if i ∈ a then some (σ i) else none) := by
    funext i
    simp only [assignment, List.mem_toFinset]
  rw [he]
  exact ha

private theorem find_for (H : Language Bool) (hH : H ∈ P) (p : Polynomial ℕ) :
    ∃ find : Word → Word,
      ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) find ∧
      ∀ φ : CNF, (∃ (a : List ℕ) (σ : Assignment), accepted H p φ a σ) →
        ∃ a v : List ℕ,
          find (encodeCNF φ) = pairB (encodeCNF (unitCNF a)) (encodeCNF (unitCNF v)) ∧
          accepted H p φ a (fun i => decide (i ∈ v)) ∧
          ∀ (b : List ℕ) (σ : Assignment), accepted H p φ b σ → a.length ≤ b.length := by
  obtain ⟨dec, hd, htime⟩ := hH
  let R : Set (Word × Word) := {q | query p q ∈ H}
  let test (q : Word × Word) := dec (query p q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hd (query p q)
  have ht : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp (query_cpt p) htime
  obtain ⟨select, hselect, hleast⟩ := select_least R p (Polynomial.C 2 * p) ⟨test, htest, ht⟩
  let find (x : Word) := emitted (endState p (x, select x))
  have hfind : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) find :=
    cpt_comp (cpt_comp (cpt_pair cpt_id hselect) (endState_cpt p)) emitted_cpt
  refine ⟨find, hfind, ?_⟩
  intro φ hex
  let x := encodeCNF φ
  have ranked (w : Word) (hp : 2 ^ w.length ≤ p.eval x.length) (hm : query p (x, w) ∈ H) :
      PEqualNP.Outside.PrefixDecideHelpers.good R p x w ∧
        PEqualNP.Outside.BoundedEnumeration.idx w ≤ (Polynomial.C 2 * p).eval x.length := by
    refine ⟨⟨Nat.lt_two_pow_self.le.trans hp, hm⟩, ?_⟩
    have hb : 2 ^ (w.length + 1) ≤ (Polynomial.C 2 * p).eval x.length := by
      rw [pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hp
    exact (Nat.le_add_right _ _).trans ((PEqualNP.Outside.BoundedEnumeration.idx_bound w).trans hb)
  obtain ⟨b, σ, hb⟩ := hex
  obtain ⟨w, _, hw, hmem⟩ := encode_candidate H p φ b σ hb
  have hselected := hleast x ⟨w, ranked w hw hmem⟩
  let code := select x
  let truncated := cut (cap p x) code
  obtain ⟨a, v, tail, he, hlen, ha⟩ := iter_valid φ [] [] truncated code.length (by simp)
  change endState p (x, code) = pack x (names a) (names v) tail at he
  have hcost : budgetCost φ a ≤ truncated.length := by
    rw [digits_cost]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hlen
    omega
  have hcap : truncated.length ≤ (p.eval x.length).size - 1 := by
    simp [truncated, cut_eq, cap_length, List.length_take]
  have hpos : 0 < (p.eval x.length).size := Nat.lt_size.mpr hw |> Nat.zero_lt_of_lt
  have hbud : 2 ^ budgetCost φ a ≤ p.eval x.length := Nat.lt_size.mp (by omega)
  refine ⟨a, v, ?_, ⟨hbud, fun i hi => (mem_distinct φ i).mp (ha i hi), ?_⟩, ?_⟩
  · unfold find
    change emitted (endState p (x, code)) = _
    rw [he]
    simp [emitted, pack, selected, setTrue, unpairB_pairB, emit_enc]
  · have hm : query p (x, code) ∈ H := hselected.1.2
    unfold query at hm
    rw [he, finish_enc] at hm
    have hv : valueOf a v = (fun i => if i ∈ a then some (decide (i ∈ v)) else none) := by
      funext i
      by_cases ha : i ∈ a <;> by_cases hv : i ∈ v <;> simp [valueOf, ha, hv]
    change encodeCNF (restrict (fun i => if i ∈ a then some (decide (i ∈ v)) else none) φ) ∈ H
    rwa [← hv]
  · intro b σ hb
    obtain ⟨w, h₁, h₂, h₃⟩ := encode_candidate H p φ b σ hb
    have hmin := length_le_of_idx_le (hselected.2 w (ranked w h₂ h₃).1)
    have htr : truncated.length ≤ code.length := by simp [truncated, cut_eq, List.length_take]
    have hc := hcost.trans (htr.trans (hmin.trans h₁))
    rw [digits_cost, digits_cost] at hc
    exact Nat.le_of_mul_le_mul_left hc (by omega)

theorem PEqualNP.Outside.LeastBudgetedPartialAssignment (H : Language Bool) (hH : H ∈ P)
    (p : Polynomial ℕ) :
    let accepts := fun (φ : CNF) (a : List ℕ) (σ : Assignment) =>
      (let m := (φ.flatMap fun c => c.map Prod.fst).toFinset.card
       2 ^ (((m - 1).size + 1) * a.length) ≤ p.eval (encodeCNF φ).length) ∧
      (∀ i ∈ a, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i) ∧
      (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
       encodeCNF (φ.filterMap fun c =>
         if c.any (fun l => ρ l.1 == some l.2) then none
         else some (c.filter fun l => (ρ l.1).isNone)) ∈ H)
    ∃ find : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) find ∧
      ∀ φ : CNF, (∃ (a : List ℕ) (σ : Assignment), accepts φ a σ) →
        ∃ a v : List ℕ,
          (let names := encodeCNF (a.map (fun i => [(i, true)]))
           let values := encodeCNF (v.map (fun i => [(i, true)]))
           find (encodeCNF φ) = List.replicate names.length true ++ false :: (names ++ values)) ∧
          a.Nodup ∧ accepts φ a (fun i => decide (i ∈ v)) ∧
          ∀ (b : List ℕ) (σ : Assignment), accepts φ b σ → a.length ≤ b.length := by
  obtain ⟨find, htime, hfind⟩ := find_for H hH p
  refine ⟨find, htime, ?_⟩
  intro φ h
  obtain ⟨a, v, hencode, ha, hmin⟩ := hfind φ h
  let σ : Assignment := fun i => decide (i ∈ v)
  have hded : accepted H p φ a.dedup σ := by
    have hc : budgetCost φ a.dedup ≤ budgetCost φ a := by
      rw [digits_cost, digits_cost]
      exact Nat.mul_le_mul_left _ a.dedup_sublist.length_le
    have he : restrictTo φ a.dedup σ = restrictTo φ a σ := by
      unfold restrictTo
      congr 1
      funext i
      simp
    exact ⟨(Nat.pow_le_pow_right (by decide) hc).trans ha.1,
      fun i hi => ha.2.1 i (List.mem_dedup.mp hi), he.symm ▸ ha.2.2⟩
  have hdup : a.Nodup := List.nodup_iff_le_length_dedup.mpr (hmin a.dedup σ hded)
  exact ⟨a, v, hencode, hdup, ha, hmin⟩
