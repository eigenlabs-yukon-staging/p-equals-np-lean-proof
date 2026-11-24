import PEqualNP.Outside.AffineRowsCorrect
import PEqualNP.Outside.PrefixDecideHelpers

namespace PEqualNP.Outside.AffineWitnessVerifier

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BooleanParityScan (Word)
open PEqualNP.Outside.UniformWitnessBitEncoding (code code_cpt)
open PEqualNP.Outside.AffineRowsMachine (check check_cpt)
open PEqualNP.Outside.AffineRowsCorrect (seedCode seed_correct_length)
open PEqualNP.Outside.AffineHash (Seed Vec hit)
open PEqualNP.Outside.BoundedWordAffineIsolation (embed)
open PEqualNP.Outside.PrefixDecideHelpers (eval_mono_nat)

def source (q : Word × Word) : Word := (unpairB q.1).1
def seed (q : Word × Word) : Word := (unpairB q.1).2
def original (q : Word × Word) : Word × Word := (source q, q.2)

theorem source_cpt : ComputableInPolyTime encodePair (fun w : Word => w) source := by
  unfold source
  exact cpt_comp (f := Prod.fst) (g := fun w : Word => (unpairB w).1) cpt_fst cpt_unpairB1

theorem seed_cpt : ComputableInPolyTime encodePair (fun w : Word => w) seed := by
  unfold seed
  exact cpt_comp (f := Prod.fst) (g := fun w : Word => (unpairB w).2) cpt_fst cpt_unpairB2

theorem original_cpt : ComputableInPolyTime encodePair encodePair original := by
  unfold original
  exact cpt_pairG (f := source) (g := Prod.snd) source_cpt cpt_snd

def limit (p : Polynomial ℕ) (q : Word × Word) : Word := un (p.eval (source q).length)

theorem limit_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun w : Word => w) (limit p) := by
  unfold limit
  exact cpt_comp (f := source) (g := fun w : Word => un (p.eval w.length)) source_cpt (L055 p)

def fixedWord (p : Polynomial ℕ) (q : Word × Word) : Word := code (limit p q) q.2

theorem fixedWord_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun w : Word => w) (fixedWord p) := by
  have hp := cpt_pairG (f := limit p) (g := Prod.snd) (limit_cpt p) cpt_snd
  unfold fixedWord
  exact cpt_comp (f := fun q : Word × Word => (limit p q, q.2))
    (g := fun q : Word × Word => code q.1 q.2) hp code_cpt

def verifyHash (p : Polynomial ℕ) (q : Word × Word) : Bool := check (seed q, fixedWord p q)

theorem verifyHash_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair Computability.encodeBool (verifyHash p) := by
  have hp := cpt_pairG (f := seed) (g := fixedWord p) seed_cpt (fixedWord_cpt p)
  unfold verifyHash
  exact cpt_comp (f := fun q : Word × Word => (seed q, fixedWord p q)) (g := check) hp check_cpt

def admissible (p : Polynomial ℕ) (dec : Word × Word → Bool) (q : Word × Word) : Bool :=
  decide (q.2.length ≤ p.eval (source q).length) && dec (original q)

theorem admissible_cpt (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool dec) :
    ComputableInPolyTime encodePair Computability.encodeBool (admissible p dec) := by
  have hn := nf_decider dec p hc
  exact cptl (cpt_comp (f := original) original_cpt hn) (fun _ => rfl)

def verify (p : Polynomial ℕ) (dec : Word × Word → Bool) (q : Word × Word) : Bool :=
  admissible p dec q && verifyHash p q

theorem verify_cpt (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool dec) :
    ComputableInPolyTime encodePair Computability.encodeBool (verify p dec) := by
  have hA := cpt_comp nfDec_polyTime (admissible_cpt p dec hc)
  have hB := cpt_comp nfDec_polyTime (verifyHash_cpt p)
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
    have hl : (unpairB z).1.length ≤ z.length := by have hh := unpairB_length z; omega
    exact ⟨w, hv.trans (eval_mono_nat p hl), hw⟩
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

def encodedSeed (b k : ℕ) (h : Seed (2 * b + 1) k) : Word := seedCode h

theorem verify_correct (p : Polynomial ℕ) (dec : Word × Word → Bool) (x w : Word) (k : ℕ)
    (f : Seed (2 * p.eval x.length + 1) k) :
    verify p dec (pairB x (encodedSeed (p.eval x.length) k f), w) = true ↔
      w.length ≤ p.eval x.length ∧ dec (x,w) = true ∧ hit f (embed (p.eval x.length) w) := by
  have step : verify p dec (pairB x (encodedSeed (p.eval x.length) k f), w) = true ↔
      (w.length ≤ p.eval x.length ∧ dec (x,w) = true) ∧
      check (seedCode f, code (un (p.eval x.length)) w) = true := by
    simp [verify, admissible, verifyHash, source, original, limit, seed, fixedWord,
      unpairB_pairB, encodedSeed]
  rw [step]
  constructor
  · rintro ⟨⟨hw, hd⟩, hh⟩
    have hm : w.length ≤ (un (p.eval x.length)).length := by simpa only [un_length] using hw
    have hf := seed_correct_length (un (p.eval x.length)) w hm _ k (un_length _) f
    exact ⟨hw, hd, hf.mp hh⟩
  · rintro ⟨hw, hd, hh⟩
    have hm : w.length ≤ (un (p.eval x.length)).length := by simpa only [un_length] using hw
    have hf := seed_correct_length (un (p.eval x.length)) w hm _ k (un_length _) f
    exact ⟨⟨hw, hd⟩, hf.mpr hh⟩

end PEqualNP.Outside.AffineWitnessVerifier
