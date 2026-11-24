import PEqualNP.Outside.SparsePatternMachine
import PEqualNP.Outside.AffineWitnessVerifier
import PEqualNP.Outside.BoundedNPWitnessIsolation

namespace PEqualNP.Outside.SparsePatternWitnessVerifier

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.SparseBoundedWordIsolation (bits isolated)
open PEqualNP.Outside.SparseCoordinateIsolation (Pattern permits)
open PEqualNP.Outside.SparsePatternMachine (patternCode patternTest patternTest_enc patternTest_cpt)
open PEqualNP.Outside.AffineWitnessVerifier
  (admissible admissible_cpt source original seed fixedWord seed_cpt fixedWord_cpt limit)
open PEqualNP.Outside.PrefixDecideHelpers (eval_mono_nat)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

def verifyPattern (p : Polynomial ℕ) (q : Word × Word) : Bool := patternTest (seed q, fixedWord p q)

theorem verifyPattern_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair Computability.encodeBool (verifyPattern p) := by
  have hp := cpt_pairG (f := seed) (g := fixedWord p) seed_cpt (fixedWord_cpt p)
  unfold verifyPattern
  exact cpt_comp (f := fun q : Word × Word => (seed q, fixedWord p q)) (g := patternTest) hp patternTest_cpt

def verify (p : Polynomial ℕ) (dec : Word × Word → Bool) (q : Word × Word) : Bool :=
  admissible p dec q && verifyPattern p q

theorem verify_cpt (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool dec) :
    ComputableInPolyTime encodePair Computability.encodeBool (verify p dec) := by
  have hA := cpt_comp nfDec_polyTime (admissible_cpt p dec hc)
  have hB := cpt_comp nfDec_polyTime (verifyPattern_cpt p)
  exact cptl (nf_restrict (nf_and hA hB)) (fun _ => by simp [nfDec_encodePair, verify, Bool.and_comm])

def queries (p : Polynomial ℕ) (dec : Word × Word → Bool) : Language Bool :=
  {z | ∃ w : Word, verify p dec (z,w) = true}

theorem queries_np (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool dec) :
    queries p dec ∈ NP := by
  refine ⟨{q | verify p dec q = true}, p, ⟨verify p dec, fun _ => Iff.rfl, verify_cpt p dec hc⟩, ?_⟩
  intro z
  change (∃ w : Word, verify p dec (z,w) = true) ↔
    ∃ w : Word, w.length ≤ p.eval z.length ∧ verify p dec (z,w) = true
  constructor
  · rintro ⟨w, hw⟩
    have hv : w.length ≤ p.eval (unpairB z).1.length := by
      simp [verify, admissible, source] at hw
      exact of_decide_eq_true hw.1.1
    have hl : (unpairB z).1.length ≤ z.length := by have h := unpairB_length z; omega
    exact ⟨w, hv.trans (eval_mono_nat p hl), hw⟩
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

theorem sound (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x s w : Word)
    (h : verify p dec (pairB x s,w) = true) : w ∈ goodWords R p x := by
  simp only [verify, admissible, source, original, Bool.and_eq_true, decide_eq_true_eq, unpairB_pairB] at h
  exact (mem_goodWords R p x w).mpr ⟨h.1.1, (hd _).mpr h.1.2⟩

theorem verify_enc (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x w : Word) (c : ℕ)
    (f : Pattern (2 * p.eval x.length + 1) c) :
    verify p dec (pairB x (patternCode f), w) = true ↔
      w ∈ goodWords R p x ∧ permits f (bits (p.eval x.length) w) := by
  simp only [verify, admissible, verifyPattern, source, original, seed, fixedWord, limit,
    unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq, patternTest_enc, mem_goodWords, hd]

theorem isolates_witness (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x : Word) (c : ℕ)
    (hs : (goodWords R p x).card ≤ c + 1) (w : Word) (hw : w ∈ goodWords R p x) :
    ∃ f : Pattern (2 * p.eval x.length + 1) c,
      ∀ v : Word, verify p dec (pairB x (patternCode f), v) = true ↔ v = w := by
  obtain ⟨f,hf⟩ := isolated (p.eval x.length) c (goodWords R p x) hs
    (fun z hz => ((mem_goodWords R p x z).mp hz).1) w hw
  refine ⟨f, ?_⟩
  intro v
  rw [verify_enc R p dec hd]
  constructor
  · rintro ⟨hv, hp⟩
    exact (hf v hv).mp hp
  · intro hv
    subst v
    exact ⟨hw, (hf w hw).mpr rfl⟩

end PEqualNP.Outside.SparsePatternWitnessVerifier

open PEqualNP.Library
open PEqualNP.Outside.SparsePatternWitnessVerifier
open PEqualNP.Outside.SparsePatternMachine (patternCode)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

theorem PEqualNP.Outside.SparsePatternWitnessVerifier :
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), DecidableInPolyTime encodePair R →
      ∃ (D : List Bool × List Bool → Bool) (K : Language Bool) (W : List Bool → Finset (List Bool))
        (encodePattern : (b c : ℕ) → (Fin c → Option (Fin (2*b+1) × Bool)) → List Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        (∀ x w, w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R) ∧
        (∀ (x s w : List Bool),
          D (List.replicate x.length true ++ false :: (x ++ s),w) = true → w ∈ W x) ∧
        ∀ (x : List Bool) (c : ℕ), (W x).card ≤ c + 1 →
          ∀ w ∈ W x, ∃ f : Fin c → Option (Fin (2 * p.eval x.length + 1) × Bool),
            ∀ v : List Bool,
              D (List.replicate x.length true ++ false :: (x ++ encodePattern (p.eval x.length) c f),v) = true
                ↔ v = w := by
  intro R p ⟨dec,hd,hc⟩
  refine ⟨verify p dec, queries p dec, goodWords R p, fun _ _ f => patternCode f,
    queries_np p dec hc, verify_cpt p dec hc, fun _ => Iff.rfl, mem_goodWords R p, ?_, ?_⟩
  · exact sound R p dec hd
  · exact isolates_witness R p dec hd
