import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace PEqualNP.Outside.SparseCoordinateSeparation

variable {ι α : Type} [DecidableEq ι] [DecidableEq (ι → α)]

def agree (C : Finset ι) (u v : ι → α) : Prop := ∀ i ∈ C, u i = v i

def separates (C : Finset ι) (S : Finset (ι → α)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, agree C u v → u = v

theorem agree_left {C : Finset ι} {u v w : ι → α}
    (h₁ : agree C u v) (h₂ : agree C u w) : agree C v w :=
  fun i hi => (h₁ i hi).symm.trans (h₂ i hi)

theorem separate (S : Finset (ι → α)) :
    ∃ C : Finset ι, C.card ≤ S.card - 1 ∧ separates C S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp [separates]⟩
  | insert u S hu ih =>
    obtain ⟨C,hC,hsep⟩ := ih
    by_cases hmatch : ∃ v ∈ S, agree C u v
    · obtain ⟨v, hv, hag⟩ := hmatch
      have hne : u ≠ v := fun h => hu (h.symm ▸ hv)
      have hp : ∃ i, u i ≠ v i := by
        by_contra hh
        push Not at hh
        exact hne (funext hh)
      obtain ⟨i, hi⟩ := hp
      refine ⟨insert i C, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hu, Nat.add_sub_cancel]
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨v,hv⟩
        have hle := Finset.card_insert_le i C
        omega
      · have hcross (w : ι → α) (hw : w ∈ S) (hh : agree (insert i C) u w) : False := by
          have hc : agree C u w := fun j hj => hh j (Finset.mem_insert_of_mem hj)
          have he : v = w := hsep v hv w hw (agree_left hag hc)
          exact hi (he.symm ▸ hh i (Finset.mem_insert_self i C))
        intro a ha b hb h
        rcases Finset.mem_insert.mp ha with rfl | haS
        · rcases Finset.mem_insert.mp hb with rfl | hbS
          · rfl
          · exact False.elim (hcross b hbS h)
        · rcases Finset.mem_insert.mp hb with rfl | hbS
          · exact False.elim (hcross a haS (fun j hj => (h j hj).symm))
          · exact hsep a haS b hbS (fun j hj => h j (Finset.mem_insert_of_mem hj))
    · refine ⟨C, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hu, Nat.add_sub_cancel]
        omega
      · intro a ha b hb h
        rcases Finset.mem_insert.mp ha with rfl | haS
        · rcases Finset.mem_insert.mp hb with rfl | hbS
          · rfl
          · exact False.elim (hmatch ⟨b,hbS,h⟩)
        · rcases Finset.mem_insert.mp hb with rfl | hbS
          · exact False.elim (hmatch ⟨a,haS,fun j hj => (h j hj).symm⟩)
          · exact hsep a haS b hbS h

end PEqualNP.Outside.SparseCoordinateSeparation

theorem PEqualNP.Outside.SparseCoordinateSeparation :
    ∀ (n : ℕ) (S : Finset (Fin n → Bool)),
      ∃ C : Finset (Fin n), C.card ≤ S.card - 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, (∀ j ∈ C, u j = v j) → u = v :=
  fun _ S => SparseCoordinateSeparation.separate S
