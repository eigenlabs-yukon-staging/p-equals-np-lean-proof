import PEqualNP.Outside.PositivePairSemantics
import PEqualNP.Outside.BackdoorSearchFacts

namespace PEqualNP.Outside.HornBackdoorBranch

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.PositivePairSemantics
open PEqualNP.Outside.BackdoorSearchFacts (vcode_bound)

def strong (a : Finset ℕ) (φ : CNF) : Prop :=
  ∀ c ∈ φ, (c.filter (fun l => l.2 && decide (l.1 ∉ a))).length ≤ 1

def selectedName (t : NamePair) (second : Bool) : ℕ := if second then t.2 else t.1

theorem pair_member {φ : CNF} {k : List ℕ} {t : NamePair} (h : firstBad k φ = some t)
    (j : Bool) :
    selectedName t j ∉ k ∧ (vcode (selectedName t j)).length ≤ (encodeCNF φ).length := by
  obtain ⟨c, hc, tail, he⟩ := firstBad_some k φ t h
  have hm : selectedName t j ∈ unassigned k c := by
    rw [he]
    cases j <;> simp [selectedName]
  obtain ⟨l, hl, heq⟩ := List.mem_map.mp hm
  obtain ⟨hlc, hnot⟩ := List.mem_filter.mp hl
  simp at hnot
  rw [← heq]
  exact ⟨hnot.2, vcode_bound hc hlc⟩

theorem pair_hits {φ : CNF} {a : Finset ℕ} {k : List ℕ} {t : NamePair}
    (h : firstBad k φ = some t) (hs : strong a φ) (hk : ∀ i ∈ k, i ∈ a) :
    ∃ j : Bool, selectedName t j ∈ a := by
  by_contra! miss
  obtain ⟨c, hc, tail, he⟩ := firstBad_some k φ t h
  let fK := fun l : Literal => l.2 && decide (l.1 ∉ k)
  let fA := fun l : Literal => l.2 && decide (l.1 ∉ a)
  have e : c.filter fA = (c.filter fK).filter fA := by
    rw [List.filter_filter]
    apply congrArg (fun f => c.filter f)
    funext l
    by_cases hm : l.1 ∈ k
    · simp [fK, fA, hm, hk _ hm]
    · by_cases hp : l.2 = true <;> simp [fK, fA, hm, hp]
  have hb := hs c hc
  change (c.filter fA).length ≤ 1 at hb
  rw [e] at hb
  change (c.filter fK).map Prod.fst = _ at he
  rcases h' : c.filter fK with _ | ⟨l₁, _ | ⟨l₂, ls⟩⟩
  · simp [h'] at he
  · simp [h'] at he
  · simp only [h', List.map_cons, List.cons.injEq] at he
    have hp₁ : l₁.2 = true := (by
      have hm : l₁ ∈ c.filter fK := by simp [h']
      have hp := (List.mem_filter.mp hm).2
      simp [fK] at hp
      exact hp.1)
    have hp₂ : l₂.2 = true := (by
      have hm : l₂ ∈ c.filter fK := by simp [h']
      have hp := (List.mem_filter.mp hm).2
      simp [fK] at hp
      exact hp.1)
    have h₁ : fA l₁ = true := by simp [fA, hp₁, he.1, show t.1 ∉ a from miss false]
    have h₂ : fA l₂ = true := by simp [fA, hp₂, he.2.1, show t.2 ∉ a from miss true]
    simp only [h', List.filter_cons, h₁, h₂, ite_true, List.length_cons] at hb
    omega

end PEqualNP.Outside.HornBackdoorBranch
