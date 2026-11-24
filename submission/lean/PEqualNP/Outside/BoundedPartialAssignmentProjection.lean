import PEqualNP.Outside.BackdoorSATQuery
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Outside.PartialAssignmentFacts

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.CnfRestrictionChoices (chosen chosen_map)
open PEqualNP.Outside.PartialAssignmentFacts (assignment valueOf_filter)
open PEqualNP.Outside.BackdoorSATQuery (query query_cpt query_enc)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

theorem PEqualNP.Outside.BoundedPartialAssignmentProjection
    (H : Language Bool) (hH : H ∈ P) (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ (φ : CNF) (a : List ℕ),
        let x := List.replicate (encodeCNF φ).length true ++
          false :: (encodeCNF φ ++ a.flatMap
            (fun i => i.bits.flatMap (fun b => [true, b]) ++ [false, true]))
        2 ^ a.length ≤ p.eval x.length →
        (x ∈ L ↔ ∃ σ : Assignment,
          let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
          encodeCNF (φ.filterMap fun c =>
            if c.any (fun l => ρ l.1 == some l.2) then none
            else some (c.filter fun l => (ρ l.1).isNone)) ∈ H) := by
  obtain ⟨dec, hd, htime⟩ := hH
  let R : Set (List Bool × List Bool) := {q | query q ∈ H}
  let test : List Bool × List Bool → Bool := fun q => dec (query q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hd (query q)
  have ttime : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp query_cpt htime
  obtain ⟨select, hselect, hfind⟩ :=
    EnumeratingSelector.select_bounded R p (Polynomial.C 2 * p) ⟨test, htest, ttime⟩
  let L : Language Bool := {x | test (x, select x) = true}
  refine ⟨L, ⟨fun x => test (x, select x), fun _ => Iff.rfl,
    cpt_comp (cpt_pair cpt_id hselect) ttime⟩, ?_⟩
  intro φ a
  let x := pairB (encodeCNF φ) (names a)
  change 2 ^ a.length ≤ p.eval x.length → (x ∈ L ↔ ∃ σ : Assignment,
    encodeCNF (restrict (fun i => if i ∈ a then some (σ i) else none) φ) ∈ H)
  intro hb
  constructor
  · intro h
    have hmem : query (x, select x) ∈ H := (htest _).mpr h
    change query (pairB (encodeCNF φ) (names a), select x) ∈ H at hmem
    rw [query_enc] at hmem
    refine ⟨fun i => decide (i ∈ chosen a (select x)), ?_⟩
    have he : valueOf a (chosen a (select x)) =
        (fun i => if i ∈ a then some (decide (i ∈ chosen a (select x))) else none) := by
      funext i
      by_cases hi : i ∈ a <;> by_cases hv : i ∈ chosen a (select x) <;>
        simp [valueOf, hi, hv]
    rwa [← he]
  · rintro ⟨σ, hs⟩
    let word := a.map σ
    have hl : word.length = a.length := by simp [word]
    have hmem : query (x, word) ∈ H := by
      change query (pairB (encodeCNF φ) (names a), a.map σ) ∈ H
      rw [query_enc, chosen_map, valueOf_filter]
      have he : assignment a.toFinset σ = (fun i => if i ∈ a then some (σ i) else none) := by
        funext i
        simp only [assignment, List.mem_toFinset]
      rwa [he]
    have hlen : word.length ≤ p.eval x.length := Nat.lt_two_pow_self.le.trans (by rwa [hl])
    have hbudget : 2 ^ (word.length + 1) ≤ (Polynomial.C 2 * p).eval x.length := by
      rw [hl, pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hb
    have hidx := (BoundedEnumeration.idx_bound word).trans hbudget
    exact (htest _).mp (hfind x ⟨word, ⟨hlen, hmem⟩, (Nat.le_add_right _ _).trans hidx⟩).2
