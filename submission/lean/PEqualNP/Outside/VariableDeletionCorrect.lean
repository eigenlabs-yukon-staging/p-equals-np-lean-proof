import PEqualNP.Outside.TwoSATDeletionBackdoor

namespace PEqualNP.Outside

open PEqualNP.Search PEqualNP.Library.SearchHelpers

def hasDeletionSet (A : CNF → Prop) (k : ℕ) (φ : CNF) : Prop :=
  ∃ xs : List ℕ, xs.length ≤ k ∧ A (eraseVariables xs φ)

private theorem erase_nil (φ : CNF) : eraseVariables [] φ = φ := by simp [eraseVariables]

theorem hasDeletionSet_zero (A : CNF → Prop) (φ : CNF) :
    hasDeletionSet A 0 φ ↔ A φ := by
  constructor
  · rintro ⟨xs,h,hA⟩
    have hz := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    rwa [hz,erase_nil] at hA
  · intro h
    exact ⟨[],Nat.zero_le _,by simpa only [erase_nil] using h⟩

private theorem erase_cons (x : ℕ) (xs : List ℕ) (φ : CNF) :
    eraseVariables (x :: xs) φ = eraseVariables xs (eraseVariable x φ) := by
  unfold eraseVariables eraseVariable
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  dsimp only [Function.comp_apply]
  rw [List.filter_filter]
  apply List.filter_congr
  intro l _
  simp [Bool.and_comm]

private theorem erase_reorder (x : ℕ) (xs : List ℕ) (h : x ∈ xs) (φ : CNF) :
    eraseVariables (x :: xs.erase x) φ = eraseVariables xs φ := by
  unfold eraseVariables
  apply List.map_congr_left
  intro c _
  apply List.filter_congr
  intro l _
  by_cases hl : l.1 = x
  · simp [hl,h]
  · simp [hl]

theorem hasDeletionSet_step (A : CNF → Prop) (k : ℕ) (φ : CNF) :
    hasDeletionSet A (k+1) φ ↔ A φ ∨
      ∃ c ∈ φ, ∃ l ∈ c, hasDeletionSet A k (eraseVariable l.1 φ) := by
  classical
  constructor
  · rintro ⟨xs,hxs,hA⟩
    by_cases hs : ∃ c ∈ φ, ∃ l ∈ c, l.1 ∈ xs
    · right
      obtain ⟨c,hc,l,hl,h⟩ := hs
      refine ⟨c,hc,l,hl,xs.erase l.1,?_,?_⟩
      · rw [List.length_erase_of_mem h]
        omega
      · rw [← erase_cons,erase_reorder _ _ h]
        exact hA
    · left
      have h : eraseVariables xs φ = φ := by
        unfold eraseVariables
        nth_rw 2 [← List.map_id φ]
        apply List.map_congr_left
        intro c hc
        change List.filter _ c = c
        rw [List.filter_eq_self]
        intro l hl
        exact decide_eq_true (fun hm => hs ⟨c,hc,l,hl,hm⟩)
      rwa [h] at hA
  · rintro (h | ⟨c,hc,l,hl,xs,hxs,ha⟩)
    · exact ⟨[],Nat.zero_le _,by simpa only [erase_nil] using h⟩
    · exact ⟨l.1 :: xs,by simpa using hxs,by rwa [erase_cons]⟩

end PEqualNP.Outside
