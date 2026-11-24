import PEqualNP.Defs
import Mathlib.Tactic

open PEqualNP.Search

theorem PEqualNP.Outside.PrefixBackdoorBudgetImproves :
    (∀ φ : CNF,
      (φ.flatMap (fun c => (c.take (c.length - 2)).map Prod.fst)).toFinset.card ≤
      (φ.flatMap (fun c => if 2 < c.length then c.map Prod.fst else [])).toFinset.card) ∧
    (∃ φ : CNF,
      (φ.flatMap (fun c => (c.take (c.length - 2)).map Prod.fst)).toFinset.card <
      (φ.flatMap (fun c => if 2 < c.length then c.map Prod.fst else [])).toFinset.card) := by
  refine ⟨?_, ⟨[[(0, true), (1, true), (2, true)]], by decide⟩⟩
  intro φ
  apply Finset.card_le_card
  intro i h
  obtain ⟨c, hc, hi⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp h)
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hi
  have hlc := List.mem_of_mem_take hl
  have hlen : 2 < c.length := by
    by_contra! hsmall
    have hz : c.length - 2 = 0 := Nat.sub_eq_zero_of_le hsmall
    simp [hz] at hl
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c, hc,
    by simp [hlen, List.mem_map.mpr ⟨l, hlc, rfl⟩]⟩)
