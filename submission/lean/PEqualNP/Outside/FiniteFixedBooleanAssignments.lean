import PEqualNP.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.FixedBooleanAssignments

def agrees {ι : Type} (S : Finset ι) (fixed f : ι → Bool) : Prop :=
  ∀ i ∈ S, f i = fixed i

noncomputable def restoreEquiv {ι : Type} [DecidableEq ι] (S : Finset ι) (fixed : ι → Bool) :
    ({f : ι → Bool // agrees S fixed f} × (S → Bool)) ≃ (ι → Bool) where
  toFun fg i := if h : i ∈ S then fg.2 ⟨i,h⟩ else fg.1.1 i
  invFun f := (⟨fun i => if i ∈ S then fixed i else f i,fun i hi => by simp [hi]⟩,
    fun i => f i.1)
  left_inv := by
    rintro ⟨⟨a,ha⟩,b⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      by_cases hi : i ∈ S
      · simp [hi,ha i hi]
      · simp [hi]
    · funext i
      simp [i.2]
  right_inv f := by
    funext i
    by_cases hi : i ∈ S <;> simp [hi]

theorem count (n : ℕ) (S : Finset (Fin n)) (fixed : Fin n → Bool) :
    (@Finset.filter (Fin n → Bool) (fun f => agrees S fixed f)
      (fun _ => Classical.propDecidable _) Finset.univ).card *
      2^S.card = 2^n := by
  classical
  let P := @Finset.filter (Fin n → Bool) (fun f => agrees S fixed f)
    (fun _ => Classical.propDecidable _) Finset.univ
  have hp : ∀ f : Fin n → Bool, f ∈ P ↔ agrees S fixed f := by simp [P]
  let e : P ≃ {f : Fin n → Bool // agrees S fixed f} :=
    Equiv.subtypeEquivRight hp
  have he : Fintype.card P = Fintype.card {f : Fin n → Bool // agrees S fixed f} :=
    Fintype.card_congr e
  have h := Fintype.card_congr (restoreEquiv S fixed)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,Fintype.card_coe,← he,Fintype.card_coe] at h
  exact h

end PEqualNP.Outside.FixedBooleanAssignments

theorem PEqualNP.Outside.FiniteFixedBooleanAssignments :
    ∀ (n : ℕ) (S : Finset (Fin n)) (fixed : Fin n → Bool),
      (@Finset.filter (Fin n → Bool) (fun f => ∀ i ∈ S, f i = fixed i)
        (fun _ => Classical.propDecidable _) Finset.univ).card *
        2^S.card = 2^n := by
  exact PEqualNP.Outside.FixedBooleanAssignments.count
