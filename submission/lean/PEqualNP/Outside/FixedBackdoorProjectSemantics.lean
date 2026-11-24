import PEqualNP.Outside.FixedBackdoorProjectCore
import PEqualNP.Outside.BackdoorSearchFacts
import PEqualNP.Outside.CnfRestrictionSemantics

namespace PEqualNP.Outside.FixedBackdoorProjectSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack formula selected setTrue finish cut_eq)
open PEqualNP.Outside.FixedBackdoorProjectCore
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.AllFormulaNames (distinct collect_enc mem_distinct)
open PEqualNP.Outside.BinaryNameChoice (choose choose_member choose_encoded)
open PEqualNP.Outside.WidthDigitClock (skip_eq)
open PEqualNP.Outside.NameDigitClock (clock_codes)
open PEqualNP.Outside.BackdoorSearchFacts (vcode_bound)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

def digits (φ : CNF) : ℕ := ((distinct φ).length - 1).size

theorem probe_enc (φ : CNF) (s v : List ℕ) (b : Word) :
    probe (pack (encodeCNF φ) (names s) (names v) b) = names (distinct φ) := by
  simp [probe, formula, pack, unpairB_pairB, collect_enc]

theorem indices_enc (φ : CNF) (s v : List ℕ) (b : Word) :
    indices (pack (encodeCNF φ) (names s) (names v) b) = b.take (digits φ) := by
  unfold indices
  rw [probe_enc]
  simp [pack, BackdoorPathCore.code, unpairB_pairB, cut_eq, un_length, names, clock_codes, digits]

theorem suffix_enc (φ : CNF) (s v : List ℕ) (b : Word) :
    suffix (pack (encodeCNF φ) (names s) (names v) b) = b.drop (digits φ) := by
  unfold suffix
  rw [probe_enc]
  simp [pack, BackdoorPathCore.code, unpairB_pairB, skip_eq, un_length, names, clock_codes, digits]

theorem step_empty (φ : CNF) (s v : List ℕ) :
    step (pack (encodeCNF φ) (names s) (names v) []) =
      pack (encodeCNF φ) (names s) (names v) [] := by
  simp [step, sel, pack, BackdoorPathCore.code, unpairB_pairB]

theorem step_no_vars (φ : CNF) (s v : List ℕ) (b : Word) (h : distinct φ = []) :
    step (pack (encodeCNF φ) (names s) (names v) b) =
      pack (encodeCNF φ) (names s) (names v) b := by
  have he := probe_enc φ s v b
  rw [h] at he
  change probe (pack (encodeCNF φ) (names s) (names v) b) = [] at he
  simp [step, he, sel]

private theorem lift_names (l : List ℕ) :
    FirstWideClause.names (l.map fun i => (i, true)) = names l := by
  simp [FirstWideClause.names, names, List.map_map, Function.comp_def]

theorem choose_actual (φ : CNF) (w : Word) (h : distinct φ ≠ []) :
    ∃ i ∈ distinct φ, choose (names (distinct φ), w) = vcode i := by
  let c : Clause := (distinct φ).map (fun i => (i, true))
  have hne : c ≠ [] := by simpa [c] using h
  obtain ⟨l, hl, he⟩ := choose_member c w hne
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact ⟨i, hi, by simpa only [c, lift_names] using he⟩

theorem choose_indexed (φ : CNF) (w : Word) (j i : ℕ)
    (hb : BinaryNameChoice.binaryValue w = j) (hi : (distinct φ)[j]? = some i) :
    choose (names (distinct φ), w) = vcode i := by
  let c : Clause := (distinct φ).map (fun i => (i, true))
  have hmem : c[j]? = some (i, true) := by
    simp [c, List.getElem?_map, hi]
  simpa only [c, lift_names] using choose_encoded c w j (i, true) hb hmem

theorem step_next (φ : CNF) (s v : List ℕ) (b : Word) (hb : b ≠ [])
    (i : ℕ) (hi : i ∈ distinct φ)
    (hc : choose (names (distinct φ), b.take (digits φ)) = vcode i) :
    step (pack (encodeCNF φ) (names s) (names v) b) =
      pack (encodeCNF φ) (names (s ++ [i]))
        (names (v ++ if (b.drop (digits φ)).headD false then [i] else []))
        (b.drop (digits φ)).tail := by
  obtain ⟨c, hm, l, hl, rfl⟩ := (mem_distinct φ i).mp hi
  have hlen := vcode_bound hm hl
  have hnames : names (distinct φ) ≠ [] := by
    intro he
    have hn := length_le_flatMap_vcode (distinct φ)
    change (distinct φ).length ≤ (names (distinct φ)).length at hn
    rw [he] at hn
    have hn' : distinct φ = [] := List.length_eq_zero_iff.mp (by simpa using hn)
    simpa [hn'] using hi
  simp only [step, chooser, probe_enc, indices_enc, suffix_enc, hc]
  simp only [pack, formula, selected, setTrue, BackdoorPathCore.code, unpairB_pairB,
    cut_eq, List.take_of_length_le hlen]
  simp only [names] at hnames
  cases hbit : b[digits φ]?.getD false <;>
    simp [sel, hb, hnames, bflag, hbit, names, List.flatMap_append]

theorem iter_valid (φ : CNF) (s v : List ℕ) (b : Word) (n : ℕ)
    (hs : ∀ i ∈ s, i ∈ distinct φ) :
    ∃ s' v' : List ℕ, ∃ b' : Word,
      step^[n] (pack (encodeCNF φ) (names s) (names v) b) =
        pack (encodeCNF φ) (names s') (names v') b' ∧
      s'.length ≤ s.length + n ∧ (∀ i ∈ s', i ∈ distinct φ) := by
  induction n generalizing s v b with
  | zero => exact ⟨s, v, b, rfl, le_rfl, hs⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases hnames : distinct φ = []
    · rw [step_no_vars _ _ _ _ hnames]
      obtain ⟨s', v', b', he, hl, ha⟩ := ih s v b hs
      exact ⟨s', v', b', he, by omega, ha⟩
    · by_cases hb : b = []
      · subst b
        rw [step_empty]
        obtain ⟨s', v', b', he, hl, ha⟩ := ih s v [] hs
        exact ⟨s', v', b', he, by omega, ha⟩
      · obtain ⟨i, hi, hc⟩ := choose_actual φ (b.take (digits φ)) hnames
        rw [step_next φ s v b hb i hi hc]
        have ht : ∀ j ∈ s ++ [i], j ∈ distinct φ := by
          intro j hj
          rcases List.mem_append.mp hj with h | h
          · exact hs j h
          · obtain rfl := List.mem_singleton.mp h
            exact hi
        obtain ⟨s', v', b', he, hlen, ha⟩ := ih _ _ _ ht
        simp only [List.length_append, List.length_singleton] at hlen
        exact ⟨s', v', b', he, by omega, ha⟩

theorem finish_enc (φ : CNF) (s v : List ℕ) (b : Word) :
    finish (pack (encodeCNF φ) (names s) (names v) b) =
      encodeCNF (restrict (valueOf s v) φ) := by
  simp only [finish, pack, formula, selected, setTrue, unpairB_pairB, run_enc]

theorem query_repr (k : ℕ) (φ : CNF) (b : Word) :
    ∃ s v : List ℕ, s.length ≤ k ∧ (∀ i ∈ s, i ∈ distinct φ) ∧
      query k (encodeCNF φ, b) = encodeCNF (restrict (valueOf s v) φ) := by
  obtain ⟨s, v, t, he, hl, ha⟩ := iter_valid φ [] [] b k (by simp)
  refine ⟨s, v, by simpa using hl, ha, ?_⟩
  change finish (step^[k] (pack (encodeCNF φ) [] [] b)) = _
  change step^[k] (pack (encodeCNF φ) [] [] b) = _ at he
  rw [he, finish_enc]

end PEqualNP.Outside.FixedBackdoorProjectSemantics
