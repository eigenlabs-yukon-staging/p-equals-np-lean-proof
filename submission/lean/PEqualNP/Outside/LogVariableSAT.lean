import PEqualNP.Outside.SatCodeCorrect
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Library.SearchHelpers.Encoding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.SatCodeDecoder PEqualNP.Outside.SatCodeCorrect
open PEqualNP.Outside.BoundedEnumeration

theorem PEqualNP.Outside.LogVariableSAT (c d : ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF,
        (φ.flatten.map Prod.fst).eraseDups.length ≤ c * Nat.log2 ((encodeCNF φ).length + 1) + d →
        (encodeCNF φ ∈ L ↔ Satisfiable φ) := by
  let R : Set (List Bool × List Bool) := {q |
    (decode q).length ≤ q.1.length ∧ SV (q.1, decode q) = true}
  let bound : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) + Polynomial.C d
  let clock : Polynomial ℕ := Polynomial.C (2 ^ (d + 1)) * (Polynomial.X + 1) ^ c
  let test : List Bool × List Bool → Bool := fun q =>
    decide ((decode q).length ≤ q.1.length) && SV (q.1, decode q)
  have htest : ∀ q, q ∈ R ↔ test q = true := by
    intro q
    simp [R, test]
  have htime : ComputableInPolyTime encodePair Computability.encodeBool test := by
    have h := cpt_comp (cpt_pairG cpt_fst decode_cpt) (nf_decider SV Polynomial.X cpt_SV)
    simpa only [Polynomial.eval_X] using h
  have hR : DecidableInPolyTime encodePair R := ⟨test, htest, htime⟩
  obtain ⟨select, hsel, hfind⟩ := EnumeratingSelector.select_bounded R bound clock hR
  let L : Language Bool := {x | test (x, select x) = true}
  have hP : L ∈ P := ⟨fun x => test (x, select x), fun _ => Iff.rfl,
    cpt_comp (cpt_pair cpt_id hsel) htime⟩
  have hsub : ∀ x, x ∈ L → x ∈ SAT := by
    intro x hx
    have hr := (htest (x, select x)).mpr hx
    exact (SV_spec x).mpr ⟨decode (x, select x), hr.1, hr.2⟩
  refine ⟨L, hP, hsub, fun φ hsize => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨ψ, henc, hsat⟩ := hsub _ hx
    rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective henc] at hsat
  · intro hsat
    obtain ⟨code, hsize', hlen, happ⟩ := code_of_sat φ hsat
    let n := (encodeCNF φ).length
    have hs : code.length ≤ c * Nat.log2 (n + 1) + d := hsize'.trans hsize
    have hb : code.length ≤ bound.eval n := by
      simp only [bound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
      exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.log2_le_self _)) _)
    have hpow : 2 ^ Nat.log2 (n + 1) ≤ n + 1 :=
      (Nat.le_log2 (by omega : n + 1 ≠ 0)).mp le_rfl
    have hg : 2 ^ (c * Nat.log2 (n + 1) + d + 1) ≤ clock.eval n := by
      simp only [clock, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      rw [Nat.add_assoc, pow_add, Nat.mul_comm c, pow_mul, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow c)
    have hidx := (BoundedEnumeration.idx_lt_of_length_le hs).trans hg
    have hgood := hfind (encodeCNF φ) ⟨code, ⟨hb, hlen, happ⟩,
      (Nat.le_add_right _ _).trans hidx⟩
    exact (htest _).mp hgood.2
