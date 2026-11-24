import PEqualNP.Library.SearchHelpers.SatVerifier
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

namespace PEqualNP.Outside.ClauseOccurrenceConflict

open PEqualNP.Search

abbrev Row (φ : CNF) := Fin φ.length
abbrev Occurrence (φ : CNF) := Σ i : Row φ, Fin φ[i].length

def literal {φ : CNF} (a : Occurrence φ) : Literal := φ[a.1][a.2]

def conflict {φ : CNF} (a b : Occurrence φ) : Prop :=
  a ≠ b ∧ (a.1 = b.1 ∨ ((literal a).1 = (literal b).1 ∧ (literal a).2 ≠ (literal b).2))

def independent {φ : CNF} (s : Finset (Occurrence φ)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ¬ conflict a b

theorem conflict_symm {φ : CNF} {a b : Occurrence φ} (h : conflict a b) : conflict b a := by
  rcases h with ⟨hab, hr | ⟨hv, hp⟩⟩
  · exact ⟨Ne.symm hab, Or.inl hr.symm⟩
  · exact ⟨Ne.symm hab, Or.inr ⟨hv.symm, Ne.symm hp⟩⟩

theorem independent_distinct_rows {φ : CNF} {s : Finset (Occurrence φ)}
    (hs : independent s) : Set.InjOn Sigma.fst (s : Set (Occurrence φ)) := by
  intro a ha b hb hr
  by_contra hne
  exact hs a ha b hb ⟨hne, Or.inl hr⟩

theorem covered_rows {φ : CNF} {s : Finset (Occurrence φ)}
    (hs : independent s) (hc : φ.length ≤ s.card) :
    ∀ i : Row φ, ∃ a ∈ s, a.1 = i := by
  classical
  have he : (s.image Sigma.fst).card = s.card :=
    Finset.card_image_of_injOn (independent_distinct_rows hs)
  have hc' : (Finset.univ : Finset (Row φ)).card ≤ (s.image Sigma.fst).card := by
    rw [he]
    simpa using hc
  have hfull : s.image Sigma.fst = (Finset.univ : Finset (Row φ)) :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hc'
  intro i
  have hi : i ∈ s.image Sigma.fst := hfull ▸ Finset.mem_univ i
  exact Finset.mem_image.mp hi

noncomputable def recover {φ : CNF} (s : Finset (Occurrence φ)) : Assignment := fun i =>
  open Classical in
  decide (∃ a ∈ s, (literal a).1 = i ∧ (literal a).2 = true)

theorem recover_agrees {φ : CNF} {s : Finset (Occurrence φ)}
    (hs : independent s) (a : Occurrence φ) (ha : a ∈ s) :
    recover s (literal a).1 = (literal a).2 := by
  classical
  cases h : (literal a).2
  · simp only [recover, decide_eq_false_iff_not]
    rintro ⟨b, hb, hv, hp⟩
    have hpol : (literal a).2 ≠ (literal b).2 := by simp [h, hp]
    have hn : a ≠ b := fun he => hpol (congrArg (fun t => (literal t).2) he)
    exact hs a ha b hb ⟨hn, Or.inr ⟨hv.symm, hpol⟩⟩
  · simp only [recover, decide_eq_true_eq]
    exact ⟨a, ha, rfl, h⟩

theorem sat_of_independent {φ : CNF} {s : Finset (Occurrence φ)}
    (hs : independent s) (hc : φ.length ≤ s.card) : Satisfiable φ := by
  refine ⟨recover s, List.all_eq_true.mpr ?_⟩
  intro c hc'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc'
  obtain ⟨⟨row, col⟩, ha, hr⟩ := covered_rows hs hc ⟨i, hi⟩
  dsimp only at hr
  subst row
  apply List.any_eq_true.mpr
  refine ⟨literal ⟨⟨i, hi⟩, col⟩, List.getElem_mem _, ?_⟩
  simp [Literal.eval, recover_agrees hs _ ha]

theorem independent_of_sat {φ : CNF} (h : Satisfiable φ) :
    ∃ s : Finset (Occurrence φ), independent s ∧ s.card = φ.length := by
  classical
  obtain ⟨σ, hs⟩ := h
  have select (i : Row φ) : ∃ j : Fin φ[i].length, Literal.eval σ φ[i][j] = true := by
    have hi := List.all_eq_true.mp hs φ[i] (List.getElem_mem i.isLt)
    obtain ⟨l, hl, ht⟩ := List.any_eq_true.mp hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hl
    exact ⟨⟨j, hj⟩, ht⟩
  let f (i : Row φ) : Occurrence φ := ⟨i, Classical.choose (select i)⟩
  have hf : Function.Injective f := fun i j h => congrArg Sigma.fst h
  have htrue (i : Row φ) : σ (literal (f i)).1 = (literal (f i)).2 := by
    simpa [f, literal, Literal.eval] using Classical.choose_spec (select i)
  refine ⟨Finset.univ.image f, ?_, by simp [Finset.card_image_of_injective _ hf]⟩
  intro a ha b hb hbad
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  rcases hbad with ⟨hne, hr | ⟨hv, hp⟩⟩
  · exact hne (congrArg f hr)
  · apply hp
    rw [← htrue i, ← htrue j, hv]

end PEqualNP.Outside.ClauseOccurrenceConflict
