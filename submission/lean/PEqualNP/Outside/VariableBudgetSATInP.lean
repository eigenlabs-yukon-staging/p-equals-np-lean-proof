import PEqualNP.Outside.SatVariableBudget
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Library.SearchHelpers.Encoding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.SatCodeDecoder PEqualNP.Outside.SatCodeCorrect
open PEqualNP.Outside.SatVariableBudget

private theorem cpt_nonempty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => !x.isEmpty) := by
  let move : Bool → Bool → Bool × Option Bool := fun _ _ => (true, none)
  have ht (l : List Bool) : fstRun move (fun b => some b) true l = [true] := by
    induction l with
    | nil => rfl
    | cons b l ih => simp [fstRun, move, ih]
  refine fst_polyTime _ _ _ move (fun b => some b) false ?_
  intro l
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, move, ht, Computability.encodeBool]

theorem PEqualNP.Outside.VariableBudgetSATInP (p : Polynomial ℕ) :
    ({x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧
      2 ^ (φ.flatten.map Prod.fst).toFinset.card ≤ p.eval x.length} : Language Bool) ∈ P := by
  let R : Set (List Bool × List Bool) := {q |
    (decode q).length ≤ q.1.length ∧ SV (q.1, decode q) = true}
  let test : List Bool × List Bool → Bool := fun q =>
    decide ((decode q).length ≤ q.1.length) && SV (q.1, decode q)
  have htest : ∀ q, q ∈ R ↔ test q = true := by
    intro q
    simp [R, test]
  have htime : ComputableInPolyTime encodePair Computability.encodeBool test := by
    have h := cpt_comp (cpt_pairG cpt_fst decode_cpt) (nf_decider SV Polynomial.X cpt_SV)
    simpa only [Polynomial.eval_X] using h
  have hR : DecidableInPolyTime encodePair R := ⟨test, htest, htime⟩
  obtain ⟨select, hsel, hfind⟩ := EnumeratingSelector.select_bounded R p (Polynomial.C 2 * p) hR
  let answer := fun x : List Bool =>
    !(sel (spend p x) [] (bflag (test (x, select x)))).isEmpty
  have hanswer : ∀ x, answer x = true ↔ spend p x ≠ [] ∧ test (x, select x) = true := by
    intro x
    cases hs : spend p x <;> cases ht : test (x, select x) <;> simp [answer, hs, ht, sel, bflag]
  have hbudget (φ : CNF) :
      spend p (encodeCNF φ) ≠ [] ↔
        2 ^ (φ.flatten.map Prod.fst).toFinset.card ≤ p.eval (encodeCNF φ).length := by
    rw [spend_enc]
    have hpos : 0 < 2 ^ (φ.flatten.map Prod.fst).toFinset.card := by positivity
    rw [show ∀ k : ℕ, un k ≠ [] ↔ 0 < k from fun k => by
      cases k <;> simp [un, List.replicate_succ]]
    exact (Nat.le_div_iff_mul_le hpos).trans (by simp)
  refine ⟨answer, ?_, ?_⟩
  · intro x
    rw [hanswer]
    constructor
    · rintro ⟨φ, rfl, hsat, hb⟩
      refine ⟨(hbudget φ).mpr hb, ?_⟩
      obtain ⟨code, hcount, hlen, happ⟩ := code_of_sat_exact φ hsat
      have hlen' : code.length ≤ p.eval (encodeCNF φ).length :=
        (Nat.lt_two_pow_self (n := code.length)).le.trans (hcount ▸ hb)
      have hpow : 2 ^ (code.length + 1) ≤ (Polynomial.C 2 * p).eval (encodeCNF φ).length := by
        rw [pow_succ, Nat.mul_comm]
        simp only [Polynomial.eval_mul, Polynomial.eval_C]
        exact Nat.mul_le_mul_left _ (hcount ▸ hb)
      have hidx := (BoundedEnumeration.idx_bound code).trans hpow
      exact (htest _).mp (hfind (encodeCNF φ)
        ⟨code, ⟨hlen', hlen, happ⟩, (Nat.le_add_right _ _).trans hidx⟩).2
    · rintro ⟨hg, ht⟩
      have hr := (htest (x, select x)).mpr ht
      obtain ⟨φ, rfl, hsat⟩ := (SV_spec x).mpr ⟨decode (x, select x), hr.1, hr.2⟩
      exact ⟨φ, rfl, hsat, (hbudget φ).mp hg⟩
  · have hf := cpt_bitFlag (cpt_comp (cpt_pair cpt_id hsel) htime)
    have h := cpt_comp (cpt_sel (spend_cpt p) (cpt_const []) hf) cpt_nonempty
    exact h
