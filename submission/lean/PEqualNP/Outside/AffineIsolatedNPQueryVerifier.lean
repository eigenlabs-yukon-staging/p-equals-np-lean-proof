import PEqualNP.Outside.AffineWitnessVerifier
import PEqualNP.Outside.BoundedNPWitnessIsolation

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.AffineWitnessVerifier (verify verify_cpt verify_correct admissible source original
  encodedSeed queries queries_np)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)
open PEqualNP.Outside.BoundedWordAffineIsolation (embed embed_injOn only_iff)
open PEqualNP.Outside.AffineHash (Seed hit width_exists bound_at_width)

theorem PEqualNP.Outside.AffineIsolatedNPQueryVerifier :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
        (W : List Bool → Finset (List Bool))
        (E : (b : ℕ) → List Bool → (Fin (2 * b + 1) → ZMod 2))
        (encodeSeed : (b k : ℕ) → (Fin k → ((Fin (2 * b + 1) → ZMod 2) × ZMod 2)) → List Bool)
        (D : List Bool × List Bool → Bool) (K : Language Bool),
        DecidableInPolyTime encodePair R ∧ K ∈ NP ∧
        ComputableInPolyTime encodePair Computability.encodeBool D ∧
        (∀ x w, w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R) ∧
        (∀ x, x ∈ L ↔ (W x).Nonempty) ∧
        (∀ b, Set.InjOn (E b) ({w : List Bool | w.length ≤ b} : Set (List Bool))) ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        (∀ x ∉ L, ∀ s : List Bool,
          (List.replicate x.length true ++ false :: (x ++ s)) ∉ K) ∧
        (∀ (x : List Bool) (k : ℕ),
          let b := p.eval x.length
          ∀ (f : Fin k → ((Fin (2 * b + 1) → ZMod 2) × ZMod 2)) (w : List Bool),
            let z := List.replicate x.length true ++ false :: (x ++ encodeSeed b k f)
            D (z,w) = true ↔ w ∈ W x ∧
              ∀ i, (∑ j : Fin (2 * b + 1), (f i).1 j * E b w j) + (f i).2 = 0) ∧
        ∀ x ∈ L,
          let b := p.eval x.length
          let n := 2 * b + 1
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ n + 2 ∧
            Fintype.card (Fin k → ((Fin n → ZMod 2) × ZMod 2)) ≤ 8 *
              ((Finset.univ : Finset (Fin k → ((Fin n → ZMod 2) × ZMod 2))).filter (fun f =>
                let z := List.replicate x.length true ++ false :: (x ++ encodeSeed b k f)
                ∃ w ∈ W x, D (z,w) = true ∧ ∀ v ∈ W x, v ≠ w → D (z,v) = false)).card := by
  intro L hL
  obtain ⟨R, p, ⟨dec, hR, hc⟩, hL⟩ := hL
  let W := goodWords R p
  have hW (x w : List Bool) : w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R := mem_goodWords R p x w
  have hL' (x : List Bool) : x ∈ L ↔ (W x).Nonempty :=
    (hL x).trans (exists_congr (fun w => (hW x w).symm))
  have correct (x : List Bool) (k : ℕ) (f : Seed (2 * p.eval x.length + 1) k) (w : List Bool) :
      verify p dec (pairB x (encodedSeed (p.eval x.length) k f),w) = true ↔
        w ∈ W x ∧ hit f (embed (p.eval x.length) w) := by
    rw [verify_correct, hW, hR]
    tauto
  refine ⟨R, p, W, embed, encodedSeed, verify p dec, queries p dec,
    ⟨dec, hR, hc⟩, queries_np p dec hc, verify_cpt p dec hc,
    hW, hL', embed_injOn, fun _ => Iff.rfl, ?_, correct, ?_⟩
  · intro x hx s hq
    obtain ⟨w, hw⟩ := hq
    change verify p dec (pairB x s, w) = true at hw
    have ha : admissible p dec (pairB x s, w) = true := by
      simp only [verify, Bool.and_eq_true] at hw
      exact hw.1
    simp only [admissible, source, original, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq] at ha
    exact hx ((hL x).mpr ⟨w, ha.1, (hR _).mpr ha.2⟩)
  · intro x hx
    let b := p.eval x.length
    let S := W x
    have hn : 0 < 2 * b + 1 := by omega
    have hsize (w : List Bool) (h : w ∈ S) : w.length ≤ b := ((hW x w).mp h).1
    have hne : (S.image (embed b)).Nonempty := ((hL' x).mp hx).image _
    obtain ⟨k, hk, hbound, hsmall, hlarge⟩ := width_exists (S.image (embed b)) hne
    refine ⟨k, hk, hbound, ?_⟩
    have hcount := bound_at_width hn (S.image (embed b)) hsmall hlarge
    let F : Finset (Seed (2 * b + 1) k) := Finset.univ
    let input (f : Seed (2 * b + 1) k) := pairB x (encodedSeed b k f)
    have eqFilters :
        F.filter (fun f => ∃ a ∈ S.image (embed b), hit f a ∧
          ∀ t ∈ S.image (embed b), t ≠ a → ¬ hit f t) =
        F.filter (fun f => ∃ w ∈ S, verify p dec (input f,w) = true ∧
          ∀ v ∈ S, v ≠ w → verify p dec (input f,v) = false) := by
      ext f
      simp only [Finset.mem_filter]
      apply and_congr_right
      intro _
      rw [only_iff b k S hsize]
      constructor
      · rintro ⟨w, hw, hhit, huniq⟩
        refine ⟨w, hw, (correct x k f w).mpr ⟨hw, hhit⟩, ?_⟩
        intro v hv hn
        cases hh : verify p dec (input f,v)
        · rfl
        · exact False.elim (huniq v hv hn ((correct x k f v).mp hh).2)
      · rintro ⟨w, hw, hhit, huniq⟩
        refine ⟨w, hw, ((correct x k f w).mp hhit).2, ?_⟩
        intro v hv hn hh
        have he := (correct x k f v).mpr ⟨hv, hh⟩
        rw [huniq v hv hn] at he
        contradiction
    change Fintype.card (Seed (2 * b + 1) k) ≤ 8 * _ at hcount ⊢
    rw [eqFilters] at hcount
    exact hcount
