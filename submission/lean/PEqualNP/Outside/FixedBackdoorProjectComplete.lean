import PEqualNP.Outside.FixedBackdoorProjectSemantics

namespace PEqualNP.Outside.FixedBackdoorProjectComplete

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack finish)
open PEqualNP.Outside.FixedBackdoorProjectCore (step endState query)
open PEqualNP.Outside.FixedBackdoorProjectSemantics
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.AllFormulaNames (distinct)
open PEqualNP.Outside.BinaryNameChoice (lowDigits lowDigits_length binaryValue_lowDigits)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

def record (d j : ℕ) (b : Bool) (tail : Word) : Word := lowDigits d j ++ b :: tail

theorem record_length (d j : ℕ) (b : Bool) (tail : Word) :
    (record d j b tail).length = (d + 1) + tail.length := by
  simp [record, lowDigits_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem step_follow (φ : CNF) (s : List ℕ) (σ : Assignment) (i : ℕ)
    (hi : i ∈ distinct φ) (j : ℕ) (hj : j < 2 ^ digits φ) (hindex : (distinct φ)[j]? = some i)
    (tail : Word) :
    let next := s ++ [i]
    step (pack (encodeCNF φ) (names s) (names (s.filter σ))
      (record (digits φ) j (σ i) tail)) = pack (encodeCNF φ) (names next) (names (next.filter σ)) tail := by
  dsimp only
  have htake : (record (digits φ) j (σ i) tail).take (digits φ) = lowDigits (digits φ) j := by
    simp [record, List.take_left', lowDigits_length]
  have hdrop : (record (digits φ) j (σ i) tail).drop (digits φ) = σ i :: tail := by
    simp [record, List.drop_left', lowDigits_length]
  have hne : record (digits φ) j (σ i) tail ≠ [] := by simp [record]
  have hchoice : BinaryNameChoice.choose
      (names (distinct φ), (record (digits φ) j (σ i) tail).take (digits φ)) = vcode i := by
    rw [htake]
    exact choose_indexed φ _ j i (binaryValue_lowDigits _ _ hj) hindex
  rw [step_next _ _ _ _ hne i hi hchoice, hdrop]
  simp only [List.headD_cons, List.tail_cons, List.filter_append]
  cases h : σ i <;> simp [h]

theorem path (φ : CNF) (s a : List ℕ) (σ : Assignment)
    (h : ∀ i ∈ a, i ∈ distinct φ) :
    ∃ b : Word, b.length = (digits φ + 1) * a.length ∧
      step^[a.length] (pack (encodeCNF φ) (names s) (names (s.filter σ)) b) =
        pack (encodeCNF φ) (names (s ++ a)) (names ((s ++ a).filter σ)) [] := by
  induction a generalizing s with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons i a ih =>
    have hi := h i (by simp)
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem hi
    have hb : j < 2 ^ digits φ := by
      have hh := Nat.lt_size_self ((distinct φ).length - 1)
      unfold digits
      omega
    have hidx : (distinct φ)[j]? = some i := by simp [List.getElem?_eq_getElem hj, he]
    obtain ⟨b, hlen, hstep⟩ := ih (s ++ [i]) (fun t ht => h t (by simp [ht]))
    refine ⟨record (digits φ) j (σ i) b, ?_, ?_⟩
    · simp only [record_length, hlen, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rw [List.length_cons, Function.iterate_succ_apply, step_follow φ s σ i hi j hb hidx b]
      simpa [List.append_assoc] using hstep

theorem query_complete (k : ℕ) (φ : CNF) (a : List ℕ) (σ : Assignment)
    (ha : a.length ≤ k) (hm : ∀ i ∈ a, i ∈ distinct φ) :
    ∃ b : Word, b.length ≤ (digits φ + 1) * k ∧
      query k (encodeCNF φ, b) = encodeCNF (restrict (valueOf a (a.filter σ)) φ) := by
  obtain ⟨b, hlen, he⟩ := path φ [] a σ hm
  refine ⟨b, hlen ▸ Nat.mul_le_mul_left (digits φ + 1) ha, ?_⟩
  have hend : endState k (encodeCNF φ, b) =
      pack (encodeCNF φ) (names a) (names (a.filter σ)) [] := by
    change step^[k] (pack (encodeCNF φ) [] [] b) = _
    simp only [List.nil_append, List.filter_nil, names, List.flatMap_nil] at he
    rw [← Nat.sub_add_cancel ha, Function.iterate_add_apply, he]
    exact Function.iterate_fixed (step_empty φ a (a.filter σ)) _
  unfold query
  rw [hend, finish_enc]

end PEqualNP.Outside.FixedBackdoorProjectComplete
