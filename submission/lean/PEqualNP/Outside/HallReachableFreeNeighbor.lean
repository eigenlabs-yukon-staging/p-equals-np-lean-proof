import PEqualNP.Defs
import Mathlib.Data.Fintype.Card

theorem PEqualNP.Outside.HallReachableFreeNeighbor :
    ∀ {ι κ : Type} [DecidableEq κ] (neighbors : ι → Finset κ) (matchLeft : ι → Option κ)
      (S : Finset ι) (start : ι),
      start ∈ S → matchLeft start = none →
      S.card ≤ (S.biUnion neighbors).card →
      (∀ y ∈ S.biUnion neighbors, ∀ i, matchLeft i = some y → i ∈ S) →
      ∃ y ∈ S.biUnion neighbors, ∀ i, matchLeft i ≠ some y := by
  classical
  intro ι κ _ neighbors matchLeft S start hStart hFree hHall hClosed
  let T := S.biUnion neighbors
  by_contra h
  push Not at h
  have hAll (y : T) : ∃ i, matchLeft i = some y.1 := h y.1 y.2
  choose f hf using hAll
  let g : T → S.erase start := fun y => ⟨f y,Finset.mem_erase.mpr
    ⟨fun he => by simpa [he,hFree] using hf y,hClosed y.1 y.2 (f y) (hf y)⟩⟩
  have hInj : Function.Injective g := by
    intro a b hEq
    have he : f a = f b := congrArg Subtype.val hEq
    apply Subtype.ext
    exact Option.some.inj ((hf a).symm.trans ((congrArg matchLeft he).trans (hf b)))
  have hCard := Fintype.card_le_of_injective g hInj
  rw [Fintype.card_coe,Fintype.card_coe,Finset.card_erase_of_mem hStart] at hCard
  have hPos := Finset.card_pos.mpr ⟨start,hStart⟩
  change S.card ≤ T.card at hHall
  omega
