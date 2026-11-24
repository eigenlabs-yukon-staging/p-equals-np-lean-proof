import PEqualNP.Outside.AffinePrefixBatchMachine

namespace PEqualNP.Outside.AffineSeedTape

open PEqualNP.Library.Universal
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.AffineHash (Seed Row Coord seed_card)
open PEqualNP.Outside.AffineRowsCorrect (rowCode bit field_bit)
open PEqualNP.Outside.AffinePrefixBatchMachine (matrixRows matrixWord matrix_length row_length)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordBlockSplit (split split_enc)

abbrev Tape (n : ℕ) := {w : Word // w.length = n}

def wordEquiv (n : ℕ) : (Fin n → Bool) ≃ Tape n where
  toFun f := ⟨List.ofFn f, List.length_ofFn⟩
  invFun w i := w.val[i.val]'(by rw [w.property]; exact i.isLt)
  left_inv f := by
    funext i
    simp
  right_inv w := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [w.property]
    · intro i hi₁ hi₂
      simp

noncomputable instance (n : ℕ) : Fintype (Tape n) := Fintype.ofEquiv _ (wordEquiv n)

theorem tape_card (n : ℕ) : Fintype.card (Tape n) = 2 ^ n := by
  rw [← Fintype.card_congr (wordEquiv n)]
  simp

theorem wire_inj : Function.Injective wire := by
  intro as
  induction as with
  | nil =>
    rintro (_ | ⟨b,bs⟩) h
    · rfl
    · have hh := congrArg List.length h
      simp only [wire, List.length_nil, pairB_length] at hh
      omega
  | cons a as ih =>
    rintro (_ | ⟨b,bs⟩) h
    · have hh := congrArg List.length h
      simp only [wire, List.length_nil, pairB_length] at hh
      omega
    · have hh := congrArg unpairB h
      simp only [wire, unpairB_pairB, Prod.mk.injEq] at hh
      rw [hh.1, ih hh.2]

theorem bit_inj : Function.Injective bit := by
  intro a b h
  have hh := congrArg PEqualNP.Outside.UniformWitnessBitEncoding.field h
  simpa [field_bit] using hh

theorem row_inj (n : ℕ) : Function.Injective (@rowCode n) := by
  intro a b h
  simp only [rowCode, List.cons.injEq] at h
  apply Prod.ext
  · have hh := List.ofFn_injective h.2
    funext i
    exact bit_inj (congrFun hh i)
  · exact bit_inj h.1

theorem rows_inj (b m : ℕ) : Function.Injective (matrixRows b m) := by
  intro f g h
  have hh := List.ofFn_injective h
  funext i
  exact row_inj _ (congrFun hh i)

theorem matrix_inj (b m : ℕ) : Function.Injective (matrixWord b m) := by
  intro f g h
  let c : Word := List.replicate (2*b+2) true
  have hc : c ≠ [] := by simp [c]
  have hw (a : Seed (2*b+1) m) :
      split (c, matrixWord b m a) = wire (matrixRows b m a) := by
    unfold matrixWord
    apply split_enc _ _ hc
    intro r hr
    simpa only [c, List.length_replicate] using row_length a r hr
  apply rows_inj b m
  apply wire_inj
  rw [← hw, ← hw, h]

def encode (b m : ℕ) (f : Seed (2*b+1) m) : Tape (m * (2*b+2)) :=
  ⟨matrixWord b m f, matrix_length b m f⟩

theorem card_match (b m : ℕ) : Fintype.card (Seed (2*b+1) m) = Fintype.card (Tape (m * (2*b+2))) := by
  rw [seed_card, tape_card, ← mul_pow, Nat.mul_comm 2, ← pow_succ, ← pow_mul]
  congr 1
  rw [Nat.mul_comm]

theorem encode_bijective (b m : ℕ) : Function.Bijective (encode b m) := by
  classical
  have hinj : Function.Injective (encode b m) :=
    fun f g h => matrix_inj b m (congrArg Subtype.val h)
  refine ⟨hinj, ?_⟩
  intro w
  let S := (Finset.univ : Finset (Seed (2*b+1) m)).image (encode b m)
  have hS : S = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    have he : S.card = Fintype.card (Seed (2*b+1) m) :=
      (Finset.card_image_of_injective _ hinj).trans Finset.card_univ
    rw [he, Finset.card_univ, card_match]
  have hmem : w ∈ S := hS ▸ Finset.mem_univ w
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hmem
  exact ⟨f, hf⟩

end PEqualNP.Outside.AffineSeedTape

theorem PEqualNP.Outside.AffineSeedTapeBijection :
    ∀ b m : ℕ, ∃ E : (Fin m → ((Fin (2*b+1) → ZMod 2) × ZMod 2)) →
        {w : List Bool // w.length = m * (2*b+2)},
      Function.Bijective E ∧
      ∀ f, (E f).val = (List.ofFn (fun i : Fin m =>
        decide ((f i).2 = 1) :: List.ofFn (fun j : Fin (2*b+1) => decide ((f i).1 j = 1)))).flatten := by
  intro b m
  exact ⟨AffineSeedTape.encode b m, AffineSeedTape.encode_bijective b m, fun _ => rfl⟩
