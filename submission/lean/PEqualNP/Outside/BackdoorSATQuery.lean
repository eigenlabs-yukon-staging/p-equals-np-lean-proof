import PEqualNP.Outside.CnfRestrictionChoices
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside.BackdoorSATQuery

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.CnfRestrictionMachine (Word run run_cpt)
open PEqualNP.Outside.CnfRestrictionChoices (choose choose_cpt choose_names chosen chosen_map)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers

def query (q : Word × Word) : Word :=
  let base := unpairB q.1
  run (base.1, pairB base.2 (choose (base.2, q.2)))

theorem query_cpt : ComputableInPolyTime encodePair (fun x : Word => x) query := by
  have hNames := cpt_comp cpt_fst cpt_unpairB2
  have hFormula := cpt_comp cpt_fst cpt_unpairB1
  have hChoice := cpt_comp (cpt_pairG hNames cpt_snd) choose_cpt
  have hPack := cpt_comp (cpt_pairG hNames hChoice) cpt_pairB
  have h := cpt_comp (cpt_pairG hFormula hPack) run_cpt
  exact h

theorem query_enc (φ : CNF) (a : List ℕ) (code : Word) :
    query (pairB (encodeCNF φ) (names a), code) =
      encodeCNF (restrict (valueOf a (chosen a code)) φ) := by
  simp only [query, unpairB_pairB, choose_names, run_enc]

theorem query_sound (φ : CNF) (a : List ℕ) (code : Word)
    (h : query (pairB (encodeCNF φ) (names a), code) ∈ KSAT 2) : Satisfiable φ := by
  obtain ⟨ψ, _, he, hsat⟩ := h
  rw [query_enc] at he
  have e := PEqualNP.Library.SearchHelpers.encodeCNF_injective he
  rw [e] at hsat
  obtain ⟨σ, hσ, _⟩ := (sat_restrict_iff _ _).mp hsat
  exact ⟨σ, hσ⟩

theorem query_complete (φ : CNF) (a : List ℕ)
    (hw : ∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ a))).length ≤ 2)
    (hsat : Satisfiable φ) :
    ∃ code : Word, code.length = a.length ∧
      query (pairB (encodeCNF φ) (names a), code) ∈ KSAT 2 := by
  obtain ⟨σ, hσ⟩ := hsat
  refine ⟨a.map σ, by simp, ?_⟩
  rw [query_enc, chosen_map]
  refine ⟨restrict (valueOf a (a.filter σ)) φ, ?_, rfl, ?_⟩
  · apply restrict_width
    intro c hc
    have e : (fun l : Literal => (valueOf a (a.filter σ) l.1).isNone) =
        (fun l : Literal => decide (l.1 ∉ a)) := by
      funext l
      by_cases hm : l.1 ∈ a <;> simp [valueOf, hm]
    rw [e]
    exact hw c hc
  · apply (sat_restrict_iff _ _).mpr
    refine ⟨σ, hσ, ?_⟩
    intro i b hb
    by_cases hm : i ∈ a
    · cases hs : σ i <;> simp [valueOf, hm, List.mem_filter, hs] at hb ⊢ <;> aesop
    · simp [valueOf, hm] at hb

end PEqualNP.Outside.BackdoorSATQuery
