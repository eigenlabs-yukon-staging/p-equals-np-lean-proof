import PEqualNP.Library.SearchHelpers.SatVerifier

namespace PEqualNP.Outside.BackdoorSearchFacts

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV

private theorem length_le_flatMap {α β : Type} (f : α → List β) {a : α} {l : List α}
    (h : a ∈ l) : (f a).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | hm
    · omega
    · have hb := ih hm
      omega

theorem vcode_bound {φ : CNF} {c : Clause} {l : Literal} (hc : c ∈ φ) (hl : l ∈ c) :
    (vcode l.1).length ≤ (encodeCNF φ).length := by
  have h₁ : (vcode l.1).length ≤ (encodeLiteral l).length := by
    simp [encodeLiteral_eq]
    omega
  have h₂ := length_le_flatMap encodeLiteral hl
  have h₃ : (c.flatMap encodeLiteral).length ≤ (encodeClause c).length := by
    simp [encodeClause]
  exact h₁.trans (h₂.trans (h₃.trans (length_le_flatMap encodeClause hc)))

theorem left_decreases (a : Finset ℕ) (k : List ℕ) (i : ℕ) (hi : i ∈ a) (hn : i ∉ k) :
    (a \ (k ++ [i]).toFinset).card < (a \ k.toFinset).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro v hv
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_append, List.mem_singleton] at hv ⊢
    exact ⟨hv.1, fun h => hv.2 (Or.inl h)⟩
  · intro he
    have him : i ∈ a \ k.toFinset := by simpa [hi, hn]
    rw [← he] at him
    simpa using him


end PEqualNP.Outside.BackdoorSearchFacts
