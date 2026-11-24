import PEqualNP.Outside.TripleObstructionSemantics

namespace PEqualNP.Outside.BackdoorBranch

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.TripleObstructionSemantics

def strong (a : Finset ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ a))).length ≤ 2

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

def selectedName (t : Triple) (j : Fin 3) : ℕ :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

theorem triple_member {φ : CNF} {k : List ℕ} {t : Triple} (h : firstBad k φ = some t)
    (j : Fin 3) :
    selectedName t j ∉ k ∧ (vcode (selectedName t j)).length ≤ (encodeCNF φ).length := by
  obtain ⟨c, hc, tail, he⟩ := firstBad_some k φ t h
  have hmem : selectedName t j ∈ unassigned k c := by
    rw [he]
    fin_cases j <;> simp [selectedName]
  obtain ⟨l, hl, heq⟩ := List.mem_map.mp hmem
  obtain ⟨hlc, hnot⟩ := List.mem_filter.mp hl
  rw [← heq]
  exact ⟨of_decide_eq_true hnot, vcode_bound hc hlc⟩

theorem triple_hits {φ : CNF} {a : Finset ℕ} {k : List ℕ} {t : Triple}
    (h : firstBad k φ = some t) (hs : strong a φ) (hk : ∀ i ∈ k, i ∈ a) :
    ∃ j : Fin 3, selectedName t j ∈ a := by
  by_contra! miss
  obtain ⟨c, hc, tail, he⟩ := firstBad_some k φ t h
  let fK := fun l : Literal => decide (l.1 ∉ k)
  let fA := fun l : Literal => decide (l.1 ∉ a)
  have e : c.filter fA = (c.filter fK).filter fA := by
    rw [List.filter_filter]
    apply congrArg (fun f => c.filter f)
    funext l
    by_cases hm : l.1 ∈ k
    · simp [fK, fA, hm, hk _ hm]
    · simp [fK, fA, hm]
  have hb := hs c hc
  change (c.filter fA).length ≤ 2 at hb
  rw [e] at hb
  change (c.filter fK).map Prod.fst = _ at he
  rcases h' : c.filter fK with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, ls⟩⟩⟩
  · simp [h'] at he
  · simp [h'] at he
  · simp [h'] at he
  · have names : l₁.1 = t.1 ∧ l₂.1 = t.2.1 ∧ l₃.1 = t.2.2 := by
      simp only [h', List.map_cons, List.cons.injEq] at he
      exact ⟨he.1, he.2.1, he.2.2.1⟩
    have h₁ : fA l₁ = true := by simp [fA, names.1, show t.1 ∉ a from miss 0]
    have h₂ : fA l₂ = true := by simp [fA, names.2.1, show t.2.1 ∉ a from miss 1]
    have h₃ : fA l₃ = true := by simp [fA, names.2.2, show t.2.2 ∉ a from miss 2]
    simp only [h', List.filter_cons, h₁, h₂, h₃, ite_true, List.length_cons] at hb
    omega

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

end PEqualNP.Outside.BackdoorBranch
