import PEqualNP.Outside.PolynomialEvaluationSeparation
import PEqualNP.Outside.UnaryPolynomialEvaluation
import PEqualNP.Outside.AffineWitnessVerifier
import PEqualNP.Outside.SparseBoundedWordIsolation
import PEqualNP.Outside.BoundedNPWitnessIsolation

namespace PEqualNP.Outside.PolynomialHashWitnessVerifier

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.UnaryPolynomialEvaluation (evaluate evaluate_cpt evaluate_correct natEval natEval_ofFn)
open PEqualNP.Outside.UniformWitnessBitEncoding (code code_len)
open PEqualNP.Outside.SparseBoundedWordIsolation (bits bits_injOn)
open PEqualNP.Outside.AffineWitnessVerifier
  (admissible admissible_cpt source original seed fixedWord seed_cpt fixedWord_cpt limit)
open PEqualNP.Outside.PrefixDecideHelpers (eval_mono_nat)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def first (s : Word) : Word := (unpairB s).1.tail
def rest (s : Word) : Word := (unpairB s).2
def second (s : Word) : Word := first (rest s)
def third (s : Word) : Word := first (rest (rest s))

def test (q : Word × Word) : Bool :=
  decide (evaluate (pairB (first q.1) (pairB (second q.1) q.2)) = third q.1)

theorem test_cpt : ComputableInPolyTime encodePair Computability.encodeBool test := by
  have hs : CPT rest := cpt_unpairB2
  have h1 : CPT first := cpt_tail1 cpt_unpairB1
  have h2 : CPT second := cpt_comp (f := rest) (g := first) hs h1
  have h3 : CPT third := cpt_comp (f := fun s => rest (rest s)) (g := first) (cpt_comp (f := rest) (g := rest) hs hs) h1
  have hh := cpt_comp (cpt_pairB2 (cpt_comp cpt_unpairB1 h1)
    (cpt_pairB2 (cpt_comp cpt_unpairB1 h2) cpt_unpairB2)) evaluate_cpt
  have heq := PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  have hv := cpt_comp (cpt_pair hh (cpt_comp cpt_unpairB1 h3)) heq
  exact cptl (cpt_comp cpt_pairB hv) (fun q => by simp [test, unpairB_pairB])

def verify (p : Polynomial ℕ) (dec : Word × Word → Bool) (q : Word × Word) : Bool :=
  admissible p dec q && test (seed q, fixedWord p q)

theorem verify_cpt (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool dec) :
    ComputableInPolyTime encodePair Computability.encodeBool (verify p dec) := by
  have hA := cpt_comp nfDec_polyTime (admissible_cpt p dec hc)
  have hp := cpt_pairG (f := seed) (g := fixedWord p) seed_cpt (fixedWord_cpt p)
  have hB := cpt_comp nfDec_polyTime (cpt_comp hp test_cpt)
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

def encodeSeed (q a b : ℕ) : Word :=
  pairB (false :: un q) (pairB (false :: un a) (pairB (false :: un b) []))

theorem verify_enc (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x w : Word) (q a b : ℕ) (hq : q > 0) :
    verify p dec (pairB x (encodeSeed q a b), w) = true ↔
      w ∈ goodWords R p x ∧ natEval a (code (un (p.eval x.length)) w) % q = b := by
  have he : evaluate (pairB (un q) (pairB (un a) (code (un (p.eval x.length)) w))) =
      un (natEval a (code (un (p.eval x.length)) w) % q) := by
    simpa only [un_length] using evaluate_correct (un q) (un a) _ (by simpa only [un_length] using hq)
  simp only [verify, admissible, source, original, test, first, second, third, rest, seed, fixedWord,
    limit, encodeSeed, unpairB_pairB, List.tail_cons, he, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, mem_goodWords, hd]
  constructor
  · rintro ⟨hb,eq⟩
    exact ⟨hb, by simpa only [un_length] using congrArg List.length eq⟩
  · rintro ⟨hb,eq⟩
    exact ⟨hb, congrArg un eq⟩

theorem ofFn_bits (b : ℕ) (w : Word) (h : w.length ≤ b) :
    List.ofFn (bits b w) = code (un b) w := by
  have hl : (code (un b) w).length = 2*b+1 := by
    simpa only [un_length] using code_len (un b) w (by simpa only [un_length] using h)
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simp [bits, List.getElem?_eq_getElem h2]

theorem residue_to_field {q : ℕ} [NeZero q] (a : ZMod q) {n : ℕ} (u : Fin n → Bool) :
    ((natEval a.val (List.ofFn u) % q : ℕ) : ZMod q) =
      ∑ i : Fin n, (if u i then 1 else 0) * a ^ i.val := by
  rw [ZMod.natCast_mod, natEval_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
  cases u i <;> simp

theorem bounded_parameters (R : Set (Word × Word)) (p : Polynomial ℕ) (x : Word) (m : ℕ)
    (hm : (goodWords R p x).card ≤ m) (w : Word) (hw : w ∈ goodWords R p x) :
    ∃ q a b : ℕ, Nat.Prime q ∧ q ≤ 2 * (m*m*(2*p.eval x.length+1)+1) ∧ a < q ∧ b < q ∧
      ∀ v ∈ goodWords R p x,
        natEval a (code (un (p.eval x.length)) v) % q = b ↔ v = w := by
  classical
  let s := goodWords R p x
  let cap := p.eval x.length
  have hc : ∀ v ∈ s, v.length ≤ cap := fun v hv => ((mem_goodWords R p x v).mp hv).1
  let S := s.image (bits cap)
  have hS : S.card = s.card :=
    Finset.card_image_of_injOn (fun u hu v hv h => bits_injOn cap (hc u hu) (hc v hv) h)
  obtain ⟨q,hq,_,hqu,a,ha⟩ := PEqualNP.Outside.PolynomialEvaluationSeparation (2*cap+1) S
  letI : NeZero q := ⟨hq.ne_zero⟩
  let b := natEval a.val (code (un cap) w) % q
  have hprod : S.card * S.card * (2*cap+1) ≤ m*m*(2*cap+1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (hS ▸ hm) (hS ▸ hm))
  refine ⟨q,a.val,b,hq,hqu.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hprod 1)),
    ZMod.val_lt a, Nat.mod_lt _ hq.pos, ?_⟩
  intro v hv
  constructor
  · intro he
    have hcast := congrArg (fun j : ℕ => (j : ZMod q)) he
    change ((natEval a.val (code (un cap) v) % q : ℕ) : ZMod q) =
      ((natEval a.val (code (un cap) w) % q : ℕ) : ZMod q) at hcast
    rw [← ofFn_bits cap v (hc _ hv), ← ofFn_bits cap w (hc _ hw),
      residue_to_field a, residue_to_field a] at hcast
    exact bits_injOn cap (hc _ hv) (hc _ hw)
      (ha (Finset.mem_image.mpr ⟨v,hv,rfl⟩) (Finset.mem_image.mpr ⟨w,hw,rfl⟩) hcast)
  · intro he
    subst v
    rfl

theorem isolates_witness (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x : Word) (m : ℕ)
    (hm : (goodWords R p x).card ≤ m) (w : Word) (hw : w ∈ goodWords R p x) :
    ∃ q a b : ℕ, Nat.Prime q ∧ q ≤ 2 * (m*m*(2*p.eval x.length+1)+1) ∧ a < q ∧ b < q ∧
      ∀ v, verify p dec (pairB x (encodeSeed q a b),v) = true ↔ v = w := by
  obtain ⟨q,a,b,hq,hql,hal,hbl,h⟩ := bounded_parameters R p x m hm w hw
  refine ⟨q,a,b,hq,hql,hal,hbl,?_⟩
  intro v
  rw [verify_enc R p dec hd x v q a b hq.pos]
  constructor
  · exact fun ⟨hv,he⟩ => (h v hv).mp he
  · intro he
    subst v
    exact ⟨hw,(h w hw).mpr rfl⟩

end PEqualNP.Outside.PolynomialHashWitnessVerifier

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.PolynomialHashWitnessVerifier
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

theorem PEqualNP.Outside.PolynomialHashWitnessVerifier :
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), DecidableInPolyTime encodePair R →
      ∃ (D : List Bool × List Bool → Bool) (K : Language Bool) (W : List Bool → Finset (List Bool))
        (E : ℕ → ℕ → ℕ → List Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        (∀ x w, w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R) ∧
        (∀ (x s w : List Bool),
          D (List.replicate x.length true ++ false :: (x ++ s),w) = true → w ∈ W x) ∧
        ∀ (x : List Bool) (m : ℕ), (W x).card ≤ m →
          ∀ w ∈ W x, ∃ q a b : ℕ,
            Nat.Prime q ∧ q ≤ 2 * (m*m*(2*p.eval x.length+1)+1) ∧ a < q ∧ b < q ∧
            ∀ v : List Bool,
              D (List.replicate x.length true ++ false :: (x ++ E q a b),v) = true ↔ v = w := by
  intro R p ⟨dec,hd,hc⟩
  refine ⟨verify p dec, queries p dec, goodWords R p, encodeSeed,
    queries_np p dec hc, verify_cpt p dec hc, fun _ => Iff.rfl, mem_goodWords R p, ?_, ?_⟩
  · exact sound R p dec hd
  · exact isolates_witness R p dec hd
