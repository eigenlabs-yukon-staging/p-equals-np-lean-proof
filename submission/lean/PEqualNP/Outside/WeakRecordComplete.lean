import PEqualNP.Outside.WeakRecordMachine

namespace PEqualNP.Outside.WeakRecordComplete

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack finish)
open PEqualNP.Outside.WeakRecordMachine
open PEqualNP.Outside.WeakWideMachine (bad finish_enc)
open PEqualNP.Outside.PartialAssignmentFacts (assignment valueOf_filter)
open PEqualNP.Outside.FirstWideClause (firstWide firstWide_some firstWide_none)
open PEqualNP.Outside.WideBackdoorBranch
open PEqualNP.Outside.BinaryNameChoice (lowDigits lowDigits_length binaryValue_lowDigits choose_encoded)
open PEqualNP.Outside.BackdoorSearchFacts (left_decreases)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.RestrictCnfHelpers

def record (digits j : ℕ) (b : Bool) (tail : Word) : Word :=
  pairB (b :: lowDigits digits j) tail

theorem record_length (digits j : ℕ) (b : Bool) (tail : Word) :
    (record digits j b tail).length = (2 * digits + 3) + tail.length := by
  simp only [record, pairB_length, List.length_cons, lowDigits_length]
  omega

theorem step_follow (digits : ℕ) (φ : CNF) (k : List ℕ) (σ : Assignment) (c : Clause)
    (h : bad φ k (k.filter σ) = some c) (j : ℕ) (l : Literal)
    (hj : j < 2 ^ digits) (hindex : c[j]? = some l) (tail : Word) :
    let k' := k ++ [l.1]
    step (pack (encodeCNF φ) (names k) (names (k.filter σ))
      (record digits j (σ l.1) tail)) =
      pack (encodeCNF φ) (names k') (names (k'.filter σ)) tail := by
  dsimp only
  have hl : l ∈ c := List.mem_of_getElem? hindex
  have hchoose : BinaryNameChoice.choose
      (FirstWideClause.names c, (unpairB (record digits j (σ l.1) tail)).1.tail) = vcode l.1 := by
    simp only [record, unpairB_pairB, List.tail_cons]
    exact choose_encoded c (lowDigits digits j) j l (binaryValue_lowDigits digits j hj) hindex
  rw [step_next _ _ _ _ c h l hl hchoose]
  simp only [record, unpairB_pairB, List.headD_cons, List.filter_append]
  cases hi : σ l.1 <;> simp [hi]

theorem path_exists (digits : ℕ) (φ : CNF) (hwidth : IsKCNF (2 ^ digits) φ) (a : Finset ℕ) (σ : Assignment)
    (hs : IsKCNF 2 (restrict (assignment a σ) φ))
    (budget : ℕ) (k : List ℕ) (hk : ∀ i ∈ k, i ∈ a)
    (hb : (a \ k.toFinset).card ≤ budget) :
    ∃ rounds ≤ budget, ∃ b : Word, ∃ k' : List ℕ,
      b.length = (2 * digits + 3) * rounds ∧ bad φ k' (k'.filter σ) = none ∧
      step^[rounds] (pack (encodeCNF φ) (names k) (names (k.filter σ)) b) =
        pack (encodeCNF φ) (names k') (names (k'.filter σ)) [] := by
  induction budget using Nat.strong_induction_on generalizing k with
  | ind n ih =>
    cases h : bad φ k (k.filter σ) with
    | none =>
      exact ⟨0, Nat.zero_le _, [], k, rfl, h, rfl⟩
    | some c =>
      have h' : firstWide (restrict (assignment k.toFinset σ) φ) = some c := by
        simpa [bad, valueOf_filter] using h
      have ⟨hmem, hwide⟩ := firstWide_some h'
      have hkA : k.toFinset ⊆ a := fun _ h => hk _ (List.mem_toFinset.mp h)
      obtain ⟨l, hl, hi⟩ := wide_hits hmem hwide hkA hs
      obtain ⟨idx, hn, he⟩ := List.getElem_of_mem hl
      let j := idx
      have hj : j < 2 ^ digits := hn.trans_le (residual_width hwidth c hmem)
      have hindex : c[j]? = some l := by
        simp [j, List.getElem?_eq_getElem hn, he]
      let i := l.1
      let new := k ++ [i]
      have hnot : i ∉ k := by
        obtain ⟨_, _, _, hnone⟩ := mem_residual hmem hl
        intro hm
        simpa [assignment, i, hm] using hnone
      have hnew : ∀ v ∈ new, v ∈ a := by
        intro v hv
        simp only [new, List.mem_append, List.mem_singleton] at hv
        rcases hv with hm | rfl
        · exact hk v hm
        · exact hi
      have hleft : (a \ new.toFinset).card < n :=
        (left_decreases a k i hi hnot).trans_le hb
      obtain ⟨rounds, hrounds, tail, k', hlen, hfinish, hstep⟩ :=
        ih (a \ new.toFinset).card hleft new hnew le_rfl
      refine ⟨rounds + 1, by omega, record digits j (σ i) tail, k', ?_, hfinish, ?_⟩
      · simp only [record_length, hlen, Nat.mul_add, Nat.mul_one]
        omega
      · rw [Function.iterate_succ_apply, step_follow digits φ k σ c h j l hj hindex tail]
        exact hstep

theorem complete_query (digits : ℕ) (φ : CNF) (hwidth : IsKCNF (2 ^ digits) φ) (a : Finset ℕ) (σ : Assignment)
    (hσ : CNF.eval σ φ = true) (hs : IsKCNF 2 (restrict (assignment a σ) φ)) :
    ∃ b : Word, b.length ≤ (2 * digits + 3) * a.card ∧ query (encodeCNF φ, b) ∈ KSAT 2 := by
  obtain ⟨rounds, hr, b, k, hlen, hdone, hstep⟩ :=
    path_exists digits φ hwidth a σ hs a.card [] (by simp) (by simp)
  refine ⟨b, hlen ▸ Nat.mul_le_mul_left (2 * digits + 3) hr, ?_⟩
  have hn : rounds ≤ b.length := by
    rw [hlen, Nat.add_mul]
    have h₃ : rounds ≤ 3 * rounds := by omega
    omega
  have he : endState (encodeCNF φ, b) =
      pack (encodeCNF φ) (names k) (names (k.filter σ)) [] := by
    change step^[b.length] (pack (encodeCNF φ) [] [] b) = _
    change step^[rounds] (pack (encodeCNF φ) [] [] b) = _ at hstep
    rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, hstep,
      Function.iterate_fixed (step_done φ k (k.filter σ) [] hdone)]
  have hp : query (encodeCNF φ, b) = encodeCNF (restrict (valueOf k (k.filter σ)) φ) := by
    unfold query
    rw [he, finish_enc]
  rw [hp]
  refine ⟨restrict (valueOf k (k.filter σ)) φ, ?_, rfl, ?_⟩
  · exact (firstWide_none _).mp hdone
  · apply (sat_restrict_iff _ _).mpr
    refine ⟨σ, hσ, ?_⟩
    intro i v hv
    by_cases hm : i ∈ k
    · cases he : σ i <;> simpa [valueOf, hm, List.mem_filter, he] using hv
    · simp [valueOf, hm] at hv

end PEqualNP.Outside.WeakRecordComplete
