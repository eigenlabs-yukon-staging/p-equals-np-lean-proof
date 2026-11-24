import PEqualNP.Outside.AffineIsolatedNPQueryVerifier
import PEqualNP.Outside.FiniteSeedPrefix

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.AffineHash (Seed)
open PEqualNP.Outside.FiniteSeedPrefix (takeRows lift_probability)

theorem PEqualNP.Outside.MaximumSeedPrefixIsolation :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (p : Polynomial ℕ) (W : List Bool → Finset (List Bool))
        (encodeSeed : (b k : ℕ) → (Fin k → ((Fin (2 * b + 1) → ZMod 2) × ZMod 2)) → List Bool)
        (D : List Bool × List Bool → Bool) (K : Language Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        (∀ x, x ∈ L ↔ (W x).Nonempty) ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        (∀ x ∉ L, ∀ s : List Bool,
          (List.replicate x.length true ++ false :: (x ++ s)) ∉ K) ∧
        ∀ x ∈ L,
          let b := p.eval x.length
          let n := 2 * b + 1
          let m := n + 2
          Fintype.card (Fin m → ((Fin n → ZMod 2) × ZMod 2)) ≤ 8 *
            ((Finset.univ : Finset (Fin m → ((Fin n → ZMod 2) × ZMod 2))).filter (fun f =>
              ∃ k : Fin (m + 1), 0 < k.val ∧
                let g (i : Fin k.val) := f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩
                let z := List.replicate x.length true ++ false :: (x ++ encodeSeed b k.val g)
                ∃ w ∈ W x, D (z,w) = true ∧ ∀ v ∈ W x, v ≠ w → D (z,v) = false)).card := by
  intro L hL
  obtain ⟨R, p, W, E, enc, D, K, hR, hK, hD, hW, hmem, hEmb, hquery, hno, hcorrect, hgood⟩ :=
    PEqualNP.Outside.AffineIsolatedNPQueryVerifier L hL
  refine ⟨p,W,enc,D,K,hK,hD,hmem,hquery,hno,?_⟩
  intro x hx
  let b := p.eval x.length
  let n := 2 * b + 1
  let m := n + 2
  obtain ⟨k, hk, hm, hg⟩ := hgood x hx
  let successful (r : ℕ) (f : Seed n r) : Prop :=
    let z := pairB x (enc b r f)
    ∃ w ∈ W x, D (z,w) = true ∧ ∀ v ∈ W x, v ≠ w → D (z,v) = false
  have hsuccessDec (r : ℕ) : DecidablePred (successful r) := by
    intro f
    unfold successful
    infer_instance
  let many (f : Seed n m) : Prop :=
    ∃ j : Fin (m + 1), 0 < j.val ∧ successful j.val (takeRows (Nat.le_of_lt_succ j.isLt) f)
  letI : DecidablePred many := by
    intro f
    unfold many
    infer_instance
  have he : Fintype.card (Seed n k) ≤ 8 * ((Finset.univ : Finset (Seed n k)).filter (successful k)).card := by
    refine hg.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card ?_))
    intro f hf
    simp only [Finset.mem_filter] at hf
    exact (@Finset.mem_filter (Seed n k) (successful k) (hsuccessDec k) Finset.univ f).mpr hf
  have hlift : Fintype.card (Seed n m) ≤ 8 * ((Finset.univ : Finset (Seed n m)).filter many).card := by
    apply lift_probability hm (successful k) many 8 he
    intro f hf
    exact ⟨⟨k, Nat.lt_succ_of_le hm⟩, hk, hf⟩
  refine hlift.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card ?_))
  intro f hf
  simp only [Finset.mem_filter]
  have hh := (@Finset.mem_filter (Seed n m) many inferInstance Finset.univ f).mp hf
  obtain ⟨hmem, j, hj, w, hw, hd, huniq⟩ := hh
  have hpref : takeRows (Nat.le_of_lt_succ j.isLt) f =
      (fun i : Fin j.val => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩) := rfl
  refine ⟨hmem, j, hj, w, hw, ?_, ?_⟩
  · change D (pairB x (enc b j.val (takeRows (Nat.le_of_lt_succ j.isLt) f)), w) = true at hd
    rwa [hpref] at hd
  · intro v hv hne
    have hu := huniq v hv hne
    change D (pairB x (enc b j.val (takeRows (Nat.le_of_lt_succ j.isLt) f)), v) = false at hu
    rwa [hpref] at hu
