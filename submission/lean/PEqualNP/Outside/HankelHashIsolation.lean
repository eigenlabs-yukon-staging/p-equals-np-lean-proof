import PEqualNP.Outside.HankelHashFibres
import PEqualNP.Outside.AffineHashIsolationBound

namespace PEqualNP.Outside.HankelHash

abbrev Seed (n k : ℕ) := Hankel n k × Vec k

theorem point_size {n k : ℕ} (x : Vec n) :
    ((Finset.univ : Finset (Seed n k)).filter (fun s => hit s x)).card = 2^(n+k) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (singleEquiv x)]
  simp [Hankel,Vec,Coord,ZMod.card]

theorem seed_size (n k : ℕ) : Fintype.card (Seed n k) = 2^k * 2^(n+k) := by
  simp [Seed,Hankel,Vec,Coord,ZMod.card,Nat.mul_comm]

set_option maxHeartbeats 1500000 in
theorem isolates_size {n k : ℕ} (S : Finset (Vec n))
    (hsmall : 2*S.card ≤ 2^k) (hlarge : 2^k ≤ 4*S.card) :
    Fintype.card (Seed n k) ≤ 8 * ((Finset.univ : Finset (Seed n k)).filter
      (fun f => ∃ s ∈ S, hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)).card := by
  let p : ℕ := 2^(n+k)
  let I := ((Finset.univ : Finset (Seed n k)).filter
    (fun f => ∃ s ∈ S, hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)).card
  have qfactor : 2^k * 2^n = p := by rw [← pow_add]; simp [p,Nat.add_comm]
  have joint_le (x y : Vec n) (hx : y ≠ x) :
      ((Finset.univ : Finset (Seed n k)).filter (fun f => hit f x ∧ hit f y)).card ≤ 2^n := by
    rw [← Fintype.card_subtype]
    have hm : 2^k * Fintype.card {s : Seed n k // hit s x ∧ hit s y} ≤ 2^k * 2^n := by
      rw [(card_fibres (k := k) x y hx.symm).2,qfactor]
    exact Nat.le_of_mul_le_mul_left hm (by positivity)
  have hh := PEqualNP.Outside.PairwiseIsolation.count_bound
    (Finset.univ : Finset (Seed n k)) S (@hit n k) p (2^n)
    (fun x _ => point_size x) (fun x _ y _ h => joint_le x y h)
  have heq : (PEqualNP.Outside.PairwiseIsolation.isolates
      (Finset.univ : Finset (Seed n k)) S hit).card = I := by
    unfold I
    congr 1
    ext f
    simp only [PEqualNP.Outside.PairwiseIsolation.isolates, Finset.mem_filter,
      Finset.mem_univ,true_and]
  have hI : S.card * p ≤ I + S.card * ((S.card-1)*2^n) := by
    rwa [heq] at hh
  have h2 : 2*(S.card-1) ≤ 2^k := by omega
  have h2' : (2*(S.card-1))*2^n ≤ p := (Nat.mul_le_mul_right _ h2).trans qfactor.le
  have hpen : 2*(S.card*((S.card-1)*2^n)) ≤ S.card*p := by
    calc
      _ = S.card*((2*(S.card-1))*2^n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2'
  have hgood : S.card*p ≤ 2*I := by omega
  calc
    Fintype.card (Seed n k) = 2^k*p := seed_size n k
    _ ≤ (4*S.card)*p := Nat.mul_le_mul_right _ hlarge
    _ = 4*(S.card*p) := Nat.mul_assoc _ _ _
    _ ≤ 4*(2*I) := Nat.mul_le_mul_left _ hgood
    _ = 8*I := by omega

theorem hit_iff {n k : ℕ} (f : Seed n k) (x : Vec n) :
    hit f x ↔ ∀ i : Fin k, (∑ j : Fin n, f.1 ⟨i.val+j.val,
      by have := i.isLt; have := j.isLt; omega⟩ * x j) + f.2 i = 0 := by
  exact ⟨fun h => congrFun h, fun h => funext h⟩

end PEqualNP.Outside.HankelHash

open PEqualNP.Outside.HankelHash

theorem PEqualNP.Outside.HankelHashIsolation :
    ∀ (n : ℕ) (S : Finset (Fin n → ZMod 2)), S.Nonempty →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n+2 ∧
        Fintype.card ((Fin (n+k) → ZMod 2) × (Fin k → ZMod 2)) ≤ 8 *
          ((Finset.univ : Finset ((Fin (n+k) → ZMod 2) × (Fin k → ZMod 2))).filter
            (fun f =>
              ∃ s ∈ S, (∀ i : Fin k, (∑ j : Fin n, f.1 ⟨i.val+j.val,
                Nat.lt_of_lt_of_le (Nat.add_lt_add i.isLt j.isLt) (Nat.le_of_eq (Nat.add_comm k n))⟩ * s j) + f.2 i = 0) ∧
                ∀ t ∈ S, t ≠ s → ¬ (∀ i : Fin k, (∑ j : Fin n, f.1 ⟨i.val+j.val,
                  Nat.lt_of_lt_of_le (Nat.add_lt_add i.isLt j.isLt) (Nat.le_of_eq (Nat.add_comm k n))⟩ * t j) + f.2 i = 0))).card := by
  intro n S hS
  obtain ⟨k,hk,hN,hs,hl⟩ := PEqualNP.Outside.AffineHash.width_exists S hS
  refine ⟨k,hk,hN,?_⟩
  have hm := isolates_size S hs hl
  refine hm.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card ?_))
  intro f hf
  obtain ⟨s,hS,hHit,hOnly⟩ := (Finset.mem_filter.mp hf).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s,hS,(hit_iff f s).mp hHit,
    fun t ht hne hz => hOnly t ht hne ((hit_iff f t).mpr hz)⟩
