import PEqualNP.Outside.LeastPrefixSelection
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.Padding
import PEqualNP.Outside.CollapseFromWitnessSearch
import PEqualNP.Outside.P_subset_NP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.LeastPrefixSelection (LexLe pref_order)
open PEqualNP.Outside (P_subset_NP CollapseFromWitnessSearch)

private def witnessCode (w : Word) : Word := pairB w []

private def coded (R : Rel) : Rel :=
  {q | q.2 = witnessCode (unpairB q.2).1 ∧ (q.1, (unpairB q.2).1) ∈ R}

private theorem coded_decidable (R : Rel) (hR : DecidableInPolyTime encodePair R) :
    DecidableInPolyTime encodePair (coded R) := by
  obtain ⟨verify, hv, hc⟩ := hR
  let check (z : Word) :=
    (sel (bflag (decide ((unpairB z).2 = witnessCode (unpairB (unpairB z).2).1))) [true]
      (sel (bflag (verify ((unpairB z).1, (unpairB (unpairB z).2).1))) [true] [])).isEmpty
  let dec (q : Word × Word) := check (pairB q.1 q.2)
  have hval := cpt_unpairB1_1 cpt_unpairB2
  have hcode := cpt_pairB2 hval (cpt_const [])
  have hEq := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF cpt_unpairB2 hcode
  have hVer := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 hval) hc)
  have hcheck : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool check := by
    have h := cpt_comp (cpt_sel hEq (cpt_const [true])
      (cpt_sel hVer (cpt_const [true]) (cpt_const []))) cpt_isEmpty
    exact h
  refine ⟨dec, ?_, cpt_comp cpt_pairB hcheck⟩
  intro q
  rcases q with ⟨x, z⟩
  by_cases h : z = witnessCode (unpairB z).1
  · have hcheck : decide (z = witnessCode (unpairB z).1) = true := decide_eq_true h
    have hd : dec (x, z) = verify (x, (unpairB z).1) := by
      cases hh : verify (x, (unpairB z).1) <;>
        simp [dec, check, unpairB_pairB, hcheck, hh, bflag, sel] <;> exact h
    rw [hd]
    change (z = witnessCode (unpairB z).1 ∧ (x, (unpairB z).1) ∈ R) ↔ _
    exact (and_iff_right h).trans (hv _)
  · simp [coded, dec, check, unpairB_pairB, sel, bflag, h]

private theorem code_order (u v : Word) (h : LexLe (witnessCode u) (witnessCode v)) :
    u.length < v.length ∨ u.length = v.length ∧ LexLe u v := by
  apply pref_order
  simpa [witnessCode, pairB, un, List.append_assoc] using h

private theorem good_code (R : Rel) (p : Polynomial ℕ) (x w : Word)
    (h : good R p x w) : good (coded R) (Polynomial.C 2 * p + 1) x (witnessCode w) := by
  have hb := h.1
  refine ⟨?_, ?_⟩
  · simp only [witnessCode, pairB_length, List.length_nil, Nat.add_zero, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
    omega
  · simpa [coded, witnessCode, unpairB_pairB] using h.2

private theorem decode_good (R : Rel) (p : Polynomial ℕ) (x z : Word)
    (h : good (coded R) (Polynomial.C 2 * p + 1) x z) :
    let w := (unpairB z).1
    z = witnessCode w ∧ good R p x w := by
  obtain ⟨hb, hz, hmem⟩ := h
  refine ⟨hz, ?_, hmem⟩
  change z = witnessCode (unpairB z).1 at hz
  conv at hb => lhs; rw [hz]
  simp only [witnessCode, pairB_length, List.length_nil, Nat.add_zero, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one] at hb
  omega

theorem PEqualNP.Outside.ShortestLexWitnessSearch :
    P = NP ↔
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
        ∃ select : List Bool → List Bool,
          ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) select ∧
          ∀ x : List Bool,
            (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
            (select x).length ≤ p.eval x.length ∧ (x, select x) ∈ R ∧
              ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
                (select x).length < v.length ∨ (select x).length = v.length ∧
                  (select x = v ∨ List.Lex (fun a b => a = false ∧ b = true) (select x) v) := by
  constructor
  · intro equality R p hR
    let Q := Polynomial.C 2 * p + 1
    have hD := coded_decidable R hR
    have hnp := extensions_np (coded R) Q hD
    rw [← equality] at hnp
    obtain ⟨s, ht, hspec⟩ := PEqualNP.Outside.LeastPrefixSelection.selector_of_extensions (coded R) Q hD hnp
    let select (x : Word) := (unpairB (s x)).1
    refine ⟨select, cpt_unpairB1_1 ht, ?_⟩
    rintro x ⟨w, hlen, hw⟩
    have hex : ∃ z, good (coded R) Q x z := ⟨witnessCode w, good_code R p x w ⟨hlen, hw⟩⟩
    obtain ⟨hgood, hmin⟩ := hspec x hex
    have ⟨he, hs⟩ := decode_good R p x (s x) hgood
    refine ⟨hs.1, hs.2, ?_⟩
    intro v hv hm
    have hlex := hmin (witnessCode v) (good_code R p x v ⟨hv, hm⟩)
    rw [he] at hlex
    exact code_order (select x) v hlex
  · intro hall
    apply Set.Subset.antisymm P_subset_NP
    apply CollapseFromWitnessSearch
    intro R p hR
    obtain ⟨s, hs, hg⟩ := hall R p hR
    exact ⟨s, hs, fun x hx => ⟨(hg x hx).1, (hg x hx).2.1⟩⟩
