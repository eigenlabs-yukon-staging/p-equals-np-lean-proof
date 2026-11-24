import PEqualNP.Outside.AffineIsolationQueryBatch
import PEqualNP.Outside.AffineSeedTapeBijection

namespace PEqualNP.Outside.FixedCoinTapeIsolation

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.AffineHash (Seed)
open PEqualNP.Outside.AffineSeedTape (Tape wordEquiv encode encode_bijective)
open PEqualNP.Outside.AffineIsolationQueryBatch (Word results successful batch_count)
open PEqualNP.Outside.AffinePrefixBatchMachine (matrixWord mem_queries produce produce_enc produce_cpt)
open PEqualNP.Outside.RecordPrefixQueries (listFrom)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt admissible source original queries queries_np)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

def tapeLength (b : ℕ) : ℕ := (2 * b + 3) * (2 * b + 2)

noncomputable def points (b : ℕ) : Seed (2 * b + 1) (2 * b + 3) ≃ (Fin (tapeLength b) → Bool) :=
  (Equiv.ofBijective (encode b (2 * b + 3)) (encode_bijective b (2 * b + 3))).trans (wordEquiv _).symm

theorem points_word (b : ℕ) (r : Fin (tapeLength b) → Bool) :
    matrixWord b (2 * b + 3) ((points b).symm r) = List.ofFn r := by
  have h := congrArg (wordEquiv (tapeLength b)) ((points b).apply_symm_apply r)
  change (wordEquiv (tapeLength b)) ((wordEquiv (tapeLength b)).symm
    (encode b (2 * b + 3) ((points b).symm r))) = (wordEquiv (tapeLength b)) r at h
  have he := (wordEquiv (tapeLength b)).apply_symm_apply
    (encode b (2 * b + 3) ((points b).symm r))
  exact congrArg Subtype.val (he.symm.trans h)

noncomputable def Q (p : Polynomial ℕ) (x : Word) (u : Fin (tapeLength (p.eval x.length)) → Bool) : List Word :=
  results p x ((points (p.eval x.length)).symm u)

theorem count_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ f, p f ↔ q (e f)) :
    ((Finset.univ : Finset α).filter p).card = ((Finset.univ : Finset β).filter q).card := by
  classical
  have he : ((Finset.univ : Finset α).filter p).image e = (Finset.univ : Finset β).filter q := by
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (h f).mp hf
    · intro hg
      exact ⟨e.symm g, (h (e.symm g)).mpr (by simpa using hg), e.apply_symm_apply g⟩
  rw [← he, Finset.card_image_of_injective _ e.injective]

def event (D : Word × Word → Bool) (S : Finset Word) (qs : List Word) : Prop :=
  ∃ z ∈ qs.toFinset, successful D S z

instance (D : Word × Word → Bool) (S : Finset Word) (qs : List Word) : Decidable (event D S qs) := by
  unfold event
  infer_instance

theorem tape_count (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x : Word) (hx : (goodWords R p x).Nonempty) :
    Fintype.card (Fin (tapeLength (p.eval x.length)) → Bool) ≤ 8 *
      ((Finset.univ : Finset (Fin (tapeLength (p.eval x.length)) → Bool)).filter
        (fun r => event (verify p dec) (goodWords R p x) (Q p x r))).card := by
  let e := points (p.eval x.length)
  have hg := batch_count R p dec hd x hx
  have he := Fintype.card_congr e
  have hf := count_equiv e
    (fun f => event (verify p dec) (goodWords R p x) (results p x f))
    (fun r => event (verify p dec) (goodWords R p x) (Q p x r)) (by
      intro f
      unfold Q
      rw [show (points (p.eval x.length)).symm (e f) = f from e.symm_apply_apply f])
  rw [← he, ← hf]
  exact hg

theorem batch_on_tape (p : Polynomial ℕ) (x : Word) (r : Fin (tapeLength (p.eval x.length)) → Bool) :
    produce p (x, List.ofFn r) =
      (Q p x r).foldr (fun y rest => List.replicate y.length true ++ false :: (y ++ rest)) [] := by
  rw [← points_word (p.eval x.length) r, produce_enc]
  change wire (Q p x r) = _
  generalize Q p x r = rows
  induction rows with
  | nil => rfl
  | cons z zs ih => simp [wire, pairB, un, ih]

theorem sound_query (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x : Word)
    (r : Fin (tapeLength (p.eval x.length)) → Bool) (z w : Word)
    (hz : z ∈ Q p x r) (hw : verify p dec (z,w) = true) : w ∈ goodWords R p x := by
  unfold Q results at hz
  obtain ⟨j, _, rfl⟩ := (mem_queries (p.eval x.length) _ x z _).mp hz
  simp only [verify, admissible, source, original, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact (mem_goodWords R p x w).mpr ⟨hw.1.1, (hd _).mpr hw.1.2⟩

end PEqualNP.Outside.FixedCoinTapeIsolation

open PEqualNP.Library
open PEqualNP.Outside.FixedCoinTapeIsolation
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt queries queries_np)
open PEqualNP.Outside.AffinePrefixBatchMachine (produce produce_cpt)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

theorem PEqualNP.Outside.FixedCoinTapeQueryIsolation :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (p : Polynomial ℕ) (W : List Bool → Finset (List Bool))
        (Q : (x : List Bool) → (Fin ((2 * p.eval x.length + 3) * (2 * p.eval x.length + 2)) → Bool) →
          List (List Bool))
        (generate : List Bool × List Bool → List Bool)
        (D : List Bool × List Bool → Bool) (K : Language Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        ComputableInPolyTime encodePair (fun w : List Bool => w) generate ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        (∀ x, x ∈ L ↔ (W x).Nonempty) ∧
        (∀ x u, generate (x, List.ofFn u) =
          (Q x u).foldr (fun y rest => List.replicate y.length true ++ false :: (y ++ rest)) []) ∧
        (∀ x u z, z ∈ Q x u → ∀ w, D (z,w) = true → w ∈ W x) ∧
        ∀ x ∈ L,
          let b := p.eval x.length
          let n := (2 * b + 3) * (2 * b + 2)
          Fintype.card (Fin n → Bool) ≤ 8 *
            ((Finset.univ : Finset (Fin n → Bool)).filter
              (fun u => ∃ z ∈ (Q x u).toFinset, ∃ w ∈ W x, D (z,w) = true ∧
                ∀ v ∈ W x, v ≠ w → D (z,v) = false)).card := by
  intro L hL
  obtain ⟨R,p,⟨dec,hd,hc⟩,hL⟩ := hL
  have hm (x : List Bool) : x ∈ L ↔ (goodWords R p x).Nonempty :=
    (hL x).trans (exists_congr (fun w => (mem_goodWords R p x w).symm))
  refine ⟨p, goodWords R p, Q p, produce p, verify p dec, queries p dec,
    queries_np p dec hc, verify_cpt p dec hc, produce_cpt p, fun _ => Iff.rfl, hm,
    batch_on_tape p, ?_, ?_⟩
  · intro x u z hz w hw
    exact sound_query R p dec hd x u z w hz hw
  · intro x hx
    exact tape_count R p dec hd x ((hm x).mp hx)
