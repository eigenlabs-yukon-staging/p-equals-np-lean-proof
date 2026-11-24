import PEqualNP.Outside.BudgetBackdoorProjectCore
import PEqualNP.Outside.FixedBackdoorProjectComplete

namespace PEqualNP.Outside.BudgetBackdoorProjectSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack finish cut cut_eq)
open PEqualNP.Outside.BudgetBackdoorProjectCore (cap cap_length step endState query)
open PEqualNP.Outside.FixedBackdoorProjectCore (suffix)
open PEqualNP.Outside.FixedBackdoorProjectSemantics (digits suffix_enc choose_actual finish_enc)
open PEqualNP.Outside.FixedBackdoorProjectComplete (record record_length)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.AllFormulaNames (distinct)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

theorem step_short (φ : CNF) (s v : List ℕ) (b : Word) (h : (b.drop (digits φ)) = []) :
    step (pack (encodeCNF φ) (names s) (names v) b) =
      pack (encodeCNF φ) (names s) (names v) b := by
  simp [step, suffix_enc, h, sel]

theorem step_eq (φ : CNF) (s v : List ℕ) (b : Word) (h : (b.drop (digits φ)) ≠ []) :
    step (pack (encodeCNF φ) (names s) (names v) b) =
      FixedBackdoorProjectCore.step (pack (encodeCNF φ) (names s) (names v) b) := by
  simp [step, suffix_enc, h, sel]

theorem iter_valid (φ : CNF) (s v : List ℕ) (b : Word) (n : ℕ)
    (hs : ∀ i ∈ s, i ∈ distinct φ) :
    ∃ s' v' : List ℕ, ∃ b' : Word,
      step^[n] (pack (encodeCNF φ) (names s) (names v) b) =
        pack (encodeCNF φ) (names s') (names v') b' ∧
      (digits φ + 1) * s'.length + b'.length ≤ (digits φ + 1) * s.length + b.length ∧
      (∀ i ∈ s', i ∈ distinct φ) := by
  induction n generalizing s v b with
  | zero => exact ⟨s, v, b, rfl, le_rfl, hs⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases hshort : b.drop (digits φ) = []
    · rw [step_short φ s v b hshort]
      exact ih s v b hs
    · rw [step_eq φ s v b hshort]
      by_cases hnames : distinct φ = []
      · rw [FixedBackdoorProjectSemantics.step_no_vars _ _ _ _ hnames]
        exact ih s v b hs
      · have hb : b ≠ [] := by intro he; simp [he] at hshort
        obtain ⟨i, hi, hc⟩ := choose_actual φ (b.take (digits φ)) hnames
        rw [FixedBackdoorProjectSemantics.step_next φ s v b hb i hi hc]
        have ht : ∀ j ∈ s ++ [i], j ∈ distinct φ := by
          intro j hj
          rcases List.mem_append.mp hj with h | h
          · exact hs j h
          · obtain rfl := List.mem_singleton.mp h
            exact hi
        obtain ⟨s', v', b', he, hlen, ha⟩ := ih _ _ _ ht
        have hpositive : 0 < (b.drop (digits φ)).length := List.length_pos_iff.mpr hshort
        have hrem : ((b.drop (digits φ)).tail).length = b.length - (digits φ + 1) := by
          rw [List.length_tail, List.length_drop]
          omega
        simp only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one] at hlen
        rw [hrem] at hlen
        simp only [List.length_drop] at hpositive
        exact ⟨s', v', b', he, by omega, ha⟩

theorem query_repr (p : Polynomial ℕ) (φ : CNF) (b : Word) (hp : 0 < p.eval (encodeCNF φ).length) :
    ∃ s v : List ℕ, 2 ^ ((digits φ + 1) * s.length) ≤ p.eval (encodeCNF φ).length ∧
      (∀ i ∈ s, i ∈ distinct φ) ∧
      query p (encodeCNF φ, b) = encodeCNF (restrict (valueOf s v) φ) := by
  let x := encodeCNF φ
  let truncated := cut (cap p x) b
  obtain ⟨s, v, tail, he, hlen, ha⟩ := iter_valid φ [] [] truncated b.length (by simp)
  have hcap : truncated.length ≤ (p.eval x.length).size - 1 := by
    simp [truncated, cut_eq, List.length_take, cap_length]
  have hpositive : 0 < (p.eval x.length).size := Nat.size_pos.mpr hp
  have hpow : 2 ^ ((digits φ + 1) * s.length) ≤ p.eval x.length := by
    apply Nat.lt_size.mp
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hlen
    omega
  refine ⟨s, v, hpow, ha, ?_⟩
  change finish (step^[b.length] (pack x [] [] truncated)) = _
  change step^[b.length] (pack x [] [] truncated) = _ at he
  rw [he, finish_enc]

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
    let word := record (digits φ) j (σ i) b
    have hdrop : word.drop (digits φ) = σ i :: b := by
      simp [word, record, List.drop_left', BinaryNameChoice.lowDigits_length]
    refine ⟨word, ?_, ?_⟩
    · simp only [word, record_length, hlen, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rw [List.length_cons, Function.iterate_succ_apply, step_eq _ _ _ _ (by simp [hdrop])]
      rw [FixedBackdoorProjectComplete.step_follow φ s σ i hi j hb hidx b]
      simpa [List.append_assoc] using hstep

theorem query_complete (p : Polynomial ℕ) (φ : CNF) (a : List ℕ) (σ : Assignment)
    (ha : 2 ^ ((digits φ + 1) * a.length) ≤ p.eval (encodeCNF φ).length)
    (hm : ∀ i ∈ a, i ∈ distinct φ) :
    ∃ b : Word, 2 ^ b.length ≤ p.eval (encodeCNF φ).length ∧
      query p (encodeCNF φ, b) = encodeCNF (restrict (valueOf a (a.filter σ)) φ) := by
  let x := encodeCNF φ
  obtain ⟨b, hlen, he⟩ := path φ [] a σ hm
  have hpow : 2 ^ b.length ≤ p.eval x.length := hlen ▸ ha
  have hcut : cut (cap p x) b = b := by
    rw [cut_eq, cap_length]
    exact List.take_of_length_le (by have ht := Nat.lt_size.mpr hpow; omega)
  have hn : a.length ≤ b.length := by
    rw [hlen, Nat.add_mul]
    simp
  refine ⟨b, hpow, ?_⟩
  have hend : endState p (x, b) =
      pack x (names a) (names (a.filter σ)) [] := by
    change step^[b.length] (pack x [] [] (cut (cap p x) b)) = _
    simp only [List.nil_append, List.filter_nil, names, List.flatMap_nil] at he
    rw [hcut, ← Nat.sub_add_cancel hn, Function.iterate_add_apply, he]
    exact Function.iterate_fixed (step_short φ a (a.filter σ) [] (by simp)) _
  unfold query
  rw [hend, finish_enc]

end PEqualNP.Outside.BudgetBackdoorProjectSemantics
