import PEqualNP.Outside.AffinePrefixBatchMachine
import PEqualNP.Outside.BoundedNPWitnessIsolation

namespace PEqualNP.Outside.AffineIsolationQueryBatch

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.AffineHash (Seed hit width_exists bound_at_width)
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt verify_correct admissible source original encodedSeed queries queries_np)
open PEqualNP.Outside.AffinePrefixBatchMachine (produce produce_cpt produce_enc matrixRows matrixWord matrix_length mem_queries)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordPrefixQueries (listFrom)
open PEqualNP.Outside.FiniteSeedPrefix (takeRows lift_probability)
open PEqualNP.Outside.BoundedWordAffineIsolation (embed only_iff)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

abbrev Word := List Bool

def successful (D : Word × Word → Bool) (S : Finset Word) (z : Word) : Prop :=
  ∃ w ∈ S, D (z,w) = true ∧ ∀ v ∈ S, v ≠ w → D (z,v) = false

instance (D : Word × Word → Bool) (S : Finset Word) (z : Word) : Decidable (successful D S z) := by
  unfold successful
  infer_instance

def results (p : Polynomial ℕ) (x : Word) (f : Seed (2 * p.eval x.length + 1) (2 * p.eval x.length + 3)) : List Word :=
  listFrom x [] (matrixRows (p.eval x.length) (2 * p.eval x.length + 3) f)

def fullSeed (b : ℕ) (f : Seed (2 * b + 1) (2 * b + 3)) : Word :=
  matrixWord b (2 * b + 3) f

private theorem from_len (x : Word) (s r : List Word) : (listFrom x s r).length = r.length := by
  induction r generalizing s with
  | nil => rfl
  | cons a r ih => simp [listFrom, ih]

private theorem wire_fold (xs : List Word) :
    wire xs = xs.foldr (fun x r => List.replicate x.length true ++ false :: (x ++ r)) [] := by
  induction xs with
  | nil => rfl
  | cons a r ih => simp [wire, pairB, un, ih]

theorem batch_count (R : Set (Word × Word)) (p : Polynomial ℕ) (dec : Word × Word → Bool)
    (hd : ∀ q, q ∈ R ↔ dec q = true) (x : Word) (hne : (goodWords R p x).Nonempty) :
    Fintype.card (Seed (2 * p.eval x.length + 1) (2 * p.eval x.length + 3)) ≤ 8 *
      ((Finset.univ : Finset (Seed (2 * p.eval x.length + 1) (2 * p.eval x.length + 3))).filter
        (fun f => ∃ z ∈ (results p x f).toFinset, successful (verify p dec) (goodWords R p x) z)).card := by
  let b := p.eval x.length
  let S := goodWords R p x
  have hn : 0 < 2 * b + 1 := by omega
  have hs (w : Word) (h : w ∈ S) : w.length ≤ b := ((mem_goodWords R p x w).mp h).1
  obtain ⟨k, hk, hm, hlo, hhi⟩ := width_exists (S.image (embed b)) (hne.image _)
  have hc := bound_at_width hn (S.image (embed b)) hlo hhi
  let F : Finset (Seed (2 * b + 1) k) := Finset.univ
  let z (f : Seed (2 * b + 1) k) := pairB x (encodedSeed b k f)
  let g (f : Seed (2 * b + 1) k) := successful (verify p dec) S (z f)
  have hcorrect (f : Seed (2 * b + 1) k) (w : Word) :
      verify p dec (z f,w) = true ↔ w ∈ S ∧ hit f (embed b w) := by
    unfold z S
    rw [verify_correct, mem_goodWords, hd]
    tauto
  have he : F.filter (fun f => ∃ a ∈ S.image (embed b), hit f a ∧
      ∀ t ∈ S.image (embed b), t ≠ a → ¬ hit f t) = F.filter g := by
    ext f
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    rw [only_iff b k S hs]
    constructor
    · rintro ⟨w, hw, hh, hu⟩
      refine ⟨w, hw, (hcorrect _ _).mpr ⟨hw,hh⟩, ?_⟩
      intro v hv hn
      cases he : verify p dec (z f,v)
      · rfl
      · exact False.elim (hu v hv hn ((hcorrect _ _).mp he).2)
    · rintro ⟨w, hw, hh, hu⟩
      refine ⟨w, hw, ((hcorrect _ _).mp hh).2, ?_⟩
      intro v hv hn hh'
      have hh₁ := (hcorrect _ _).mpr ⟨hv,hh'⟩
      rw [hu v hv hn] at hh₁
      contradiction
  change Fintype.card (Seed (2 * b + 1) k) ≤ 8 *
    (F.filter (fun f => ∃ a ∈ S.image (embed b), hit f a ∧ ∀ t ∈ S.image (embed b), t ≠ a → ¬ hit f t)).card at hc
  rw [he] at hc
  apply lift_probability hm g _ 8 hc
  intro f hf
  let j : Fin (2 * b + 4) := ⟨k, by omega⟩
  refine ⟨z (takeRows hm f), List.mem_toFinset.mpr ?_, hf⟩
  exact (mem_queries b (2 * b + 3) x _ f).mpr ⟨j, hk, rfl⟩

end PEqualNP.Outside.AffineIsolationQueryBatch

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.AffineIsolationQueryBatch
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt admissible source original queries queries_np)
open PEqualNP.Outside.AffinePrefixBatchMachine (produce produce_cpt produce_enc matrixRows matrix_length mem_queries)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)

theorem PEqualNP.Outside.AffineIsolationQueryBatch :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (p : Polynomial ℕ) (W : List Bool → Finset (List Bool))
        (sample : (b : ℕ) → (Fin (2 * b + 3) → ((Fin (2 * b + 1) → ZMod 2) × ZMod 2)) → List Bool)
        (Q : (x : List Bool) → (Fin (2 * p.eval x.length + 3) →
          ((Fin (2 * p.eval x.length + 1) → ZMod 2) × ZMod 2)) → List (List Bool))
        (generate : List Bool × List Bool → List Bool)
        (D : List Bool × List Bool → Bool) (K : Language Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        ComputableInPolyTime encodePair (fun w : List Bool => w) generate ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        (∀ b f, (sample b f).length = (2 * b + 3) * (2 * b + 2)) ∧
        (∀ x f, (Q x f).length = 2 * p.eval x.length + 3 ∧
          generate (x, sample (p.eval x.length) f) =
            (Q x f).foldr (fun y r => List.replicate y.length true ++ false :: (y ++ r)) []) ∧
        (∀ x ∉ L, ∀ f, ∀ z ∈ Q x f, z ∉ K) ∧
        ∀ x ∈ L,
          let b := p.eval x.length
          Fintype.card (Fin (2 * b + 3) → ((Fin (2 * b + 1) → ZMod 2) × ZMod 2)) ≤ 8 *
            ((Finset.univ : Finset (Fin (2 * b + 3) → ((Fin (2 * b + 1) → ZMod 2) × ZMod 2))).filter
              (fun f => ∃ z ∈ (Q x f).toFinset, ∃ w ∈ W x, D (z,w) = true ∧
                ∀ v ∈ W x, v ≠ w → D (z,v) = false)).card := by
  intro L hL
  obtain ⟨R,p,⟨dec,hd,hc⟩,hL⟩ := hL
  refine ⟨p, goodWords R p, fullSeed, results p, produce p, verify p dec, queries p dec,
    queries_np p dec hc, verify_cpt p dec hc, produce_cpt p, fun _ => Iff.rfl, ?_, ?_, ?_, ?_⟩
  · intro b f
    exact matrix_length b _ f
  · intro x f
    constructor
    · rw [results, from_len]
      simp [matrixRows]
    · rw [fullSeed, produce_enc, wire_fold]
      rfl
  · intro x hx f z hz hK
    obtain ⟨j, _, rfl⟩ := (mem_queries (p.eval x.length) _ x _ f).mp hz
    obtain ⟨w, hw⟩ := hK
    simp only [verify, admissible, source, original, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact hx ((hL x).mpr ⟨w, hw.1.1, (hd _).mpr hw.1.2⟩)
  · intro x hx
    have hn : (goodWords R p x).Nonempty := (exists_congr (fun w => (mem_goodWords R p x w).symm)).mp ((hL x).mp hx)
    exact batch_count R p dec hd x hn
