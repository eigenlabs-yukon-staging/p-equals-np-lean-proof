import PEqualNP.Outside.BackdoorSATQuery
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Library.L030

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.CnfRestrictionSemantics (names)
open PEqualNP.Outside.BackdoorSATQuery (query query_cpt query_sound query_complete)

theorem PEqualNP.Outside.TwoSatBackdoorInP (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧
      ∀ (φ : CNF) (a : List ℕ),
        let x := List.replicate (encodeCNF φ).length true ++
          false :: (encodeCNF φ ++ a.flatMap
            (fun i => i.bits.flatMap (fun b => [true, b]) ++ [false, true]))
        (x ∈ L → Satisfiable φ) ∧
        ((∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ a))).length ≤ 2) →
          2 ^ a.length ≤ p.eval x.length →
          Satisfiable φ → x ∈ L) := by
  obtain ⟨dec, hdec, htime⟩ := L030
  let R : Set (List Bool × List Bool) := {q | query q ∈ KSAT 2}
  let test : List Bool × List Bool → Bool := fun q => dec (query q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hdec (query q)
  have ttime : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp query_cpt htime
  obtain ⟨select, hselect, hfind⟩ :=
    EnumeratingSelector.select_bounded R p (Polynomial.C 2 * p) ⟨test, htest, ttime⟩
  let L : Language Bool := {x | test (x, select x) = true}
  refine ⟨L, ⟨fun x => test (x, select x), fun _ => Iff.rfl,
    cpt_comp (cpt_pair cpt_id hselect) ttime⟩, ?_⟩
  intro φ a
  let x := pairB (encodeCNF φ) (names a)
  change (x ∈ L → Satisfiable φ) ∧
    ((∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ a))).length ≤ 2) →
      2 ^ a.length ≤ p.eval x.length → Satisfiable φ → x ∈ L)
  constructor
  · intro h
    exact query_sound φ a (select x) ((htest _).mpr h)
  · intro hw hb hsat
    obtain ⟨code, hlen, hmem⟩ := query_complete φ a hw hsat
    have hlen' : code.length ≤ p.eval x.length :=
      Nat.lt_two_pow_self.le.trans (by rwa [hlen])
    have hbudget : 2 ^ (code.length + 1) ≤ (Polynomial.C 2 * p).eval x.length := by
      rw [hlen, pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hb
    have hidx := (BoundedEnumeration.idx_bound code).trans hbudget
    exact (htest _).mp (hfind x ⟨code, ⟨hlen', hmem⟩, (Nat.le_add_right _ _).trans hidx⟩).2
