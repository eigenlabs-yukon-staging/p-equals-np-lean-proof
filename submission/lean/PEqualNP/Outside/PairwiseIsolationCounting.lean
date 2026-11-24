import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace PEqualNP.Outside.PairwiseIsolation

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def only (H : Finset α) (S : Finset β) (hit : α → β → Prop) [DecidableRel hit] (s : β) : Finset α :=
  H.filter (fun f => hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)

def collision (H : Finset α) (hit : α → β → Prop) [DecidableRel hit] (s t : β) : Finset α :=
  H.filter (fun f => hit f s ∧ hit f t)

def isolates (H : Finset α) (S : Finset β) (hit : α → β → Prop) [DecidableRel hit] : Finset α :=
  H.filter (fun f => ∃ s ∈ S, hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)

theorem isolation_count (H : Finset α) (S : Finset β) (hit : α → β → Prop) [DecidableRel hit] :
    (isolates H S hit).card = ∑ s ∈ S, (only H S hit s).card := by
  classical
  have he : isolates H S hit = S.biUnion (only H S hit) := by
    ext f
    simp only [isolates, only, Finset.mem_biUnion, Finset.mem_filter]
    aesop
  rw [he, Finset.card_biUnion]
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro f hf hg
  have h₁ := (Finset.mem_filter.mp hf).2
  have h₂ := (Finset.mem_filter.mp hg).2
  exact h₁.2 b hb (Ne.symm hab) h₂.1

theorem per_element (H : Finset α) (S : Finset β) (hit : α → β → Prop) [DecidableRel hit]
    (s : β) (hs : s ∈ S) (p q : ℕ)
    (hmarginal : (H.filter (fun f => hit f s)).card = p)
    (hpair : ∀ t ∈ S, t ≠ s → (collision H hit s t).card ≤ q) :
    p ≤ (only H S hit s).card + (S.card - 1) * q := by
  classical
  let target := H.filter (fun f => hit f s)
  let colliding := (S.erase s).biUnion (collision H hit s)
  have hcover : target ⊆ (only H S hit s) ∪ colliding := by
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    by_cases he : ∀ t ∈ S, t ≠ s → ¬ hit f t
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hf'.1, hf'.2, he⟩))
    · push Not at he
      obtain ⟨t, ht, hne, hv⟩ := he
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_erase.mpr ⟨hne, ht⟩, Finset.mem_filter.mpr ⟨hf'.1, hf'.2, hv⟩⟩))
  have hc : colliding.card ≤ (S.card - 1) * q := by
    unfold colliding
    rw [← Finset.card_erase_of_mem hs]
    apply Finset.card_biUnion_le_card_mul
    intro t ht
    exact hpair t (Finset.mem_erase.mp ht).2 (Finset.mem_erase.mp ht).1
  calc
    p = target.card := hmarginal.symm
    _ ≤ ((only H S hit s) ∪ colliding).card := Finset.card_le_card hcover
    _ ≤ (only H S hit s).card + colliding.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left hc _

theorem count_bound
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (H : Finset α) (S : Finset β) (hit : α → β → Prop) [DecidableRel hit] (p q : ℕ)
    (hmarginal : ∀ s ∈ S, (H.filter (fun f => hit f s)).card = p)
    (hpair : ∀ s ∈ S, ∀ t ∈ S, t ≠ s → (H.filter (fun f => hit f s ∧ hit f t)).card ≤ q) :
    S.card * p ≤
      (isolates H S hit).card +
        S.card * ((S.card - 1) * q) := by
  classical
  have h := Finset.sum_le_sum (s := S) (fun s hs =>
    per_element H S hit s hs p q (hmarginal s hs) (hpair s hs))
  rwa [Finset.sum_const, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul, ← isolation_count] at h

end PEqualNP.Outside.PairwiseIsolation

open PEqualNP.Outside.PairwiseIsolation

theorem PEqualNP.Outside.PairwiseIsolationCounting
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (H : Finset α) (S : Finset β) (hit : α → β → Prop) [DecidableRel hit] (p q : ℕ)
    (hmarginal : ∀ s ∈ S, (H.filter (fun f => hit f s)).card = p)
    (hpair : ∀ s ∈ S, ∀ t ∈ S, t ≠ s → (H.filter (fun f => hit f s ∧ hit f t)).card ≤ q) :
    S.card * p ≤
      (H.filter (fun f => ∃ s ∈ S, hit f s ∧ ∀ t ∈ S, t ≠ s → ¬ hit f t)).card +
        S.card * ((S.card - 1) * q) :=
  count_bound H S hit p q hmarginal hpair
