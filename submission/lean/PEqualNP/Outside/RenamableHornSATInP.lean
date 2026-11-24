import PEqualNP.Outside.RenamableHornReducesToTwoSAT
import PEqualNP.Outside.TwoSatGreedySemantics
import PEqualNP.Outside.HornSATSublanguageInP
import PEqualNP.Library.SearchHelpers.Encoding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.HornRenamingFacts
open PEqualNP.Outside.HornRenamingCompiler (compile compile_cpt compile_enc)
open PEqualNP.Outside.HornRenameMachine (flips run run_cpt run_enc)
open PEqualNP.Outside.TwoSatGreedyCore (finish finish_cpt)
open PEqualNP.Outside.TwoSatGreedySemantics (solve)
open PEqualNP.Outside (HornSATSublanguageInP)

private theorem wfFlag_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem pairClause_vars (d c : Clause) (hc : d ∈ pairClauses c) :
    ∀ l ∈ d, l ∈ c := by
  induction c with
  | nil => simp [pairClauses] at hc
  | cons a c ih =>
    simp only [pairClauses, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨b, hb, rfl⟩ | hd
    · intro l hl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · simp
      · exact List.mem_cons_of_mem _ hb
    · exact fun l hl => List.mem_cons_of_mem _ (ih hd l hl)

private theorem pair_vars (φ : CNF) (c : Clause) (hc : c ∈ pairCNF φ) (l : Literal) (hl : l ∈ c) :
    ∃ d ∈ φ, ∃ r ∈ d, r.1 = l.1 := by
  obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp hc
  exact ⟨d, hd, l, pairClause_vars c d he l hl, rfl⟩

private theorem renamable_iff (φ : CNF) :
    Satisfiable (pairCNF φ) ↔ ∃ ρ : Assignment, ∀ c ∈ φ,
      (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1 := by
  refine exists_congr (fun ρ => (pairCNF_correct ρ φ).trans ?_)
  constructor
  · intro h c hc
    have he := h (renameClause ρ c) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    simpa [renameClause, List.filter_map, Function.comp_def] using he
  · intro h d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    simpa [renameClause, List.filter_map, Function.comp_def] using h c hc

private theorem pair_membership (φ : CNF) :
    encodeCNF (pairCNF φ) ∈ KSAT 2 ↔ Satisfiable (pairCNF φ) := by
  constructor
  · rintro ⟨ψ, _, he, hs⟩
    rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
  · exact fun h => ⟨pairCNF φ, pairCNF_two φ, rfl, h⟩

theorem PEqualNP.Outside.RenamableHornSATInP :
    ({x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ Satisfiable φ ∧
      ∃ ρ : Assignment, ∀ c ∈ φ,
        (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1} : Language Bool) ∈ P := by
  obtain ⟨dec₂, hd₂, hc₂⟩ := L030
  obtain ⟨H, ⟨decH, hdH, hcH⟩, _, hHorn⟩ := HornSATSublanguageInP
  let flipNames (x : List Bool) := finish dec₂ (x, compile x)
  let transformed (x : List Bool) := run (x, flipNames x)
  let query₂ (x : List Bool) := dec₂ (compile x)
  let queryH (x : List Bool) := decH (transformed x)
  let answer (x : List Bool) :=
    (sel (bflag (wfB x)) [true]
      (sel (bflag (query₂ x)) [true] (sel (bflag (queryH x)) [true] []))).isEmpty
  have hflip : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) flipNames := by
    have h := cpt_comp (cpt_pair cpt_id compile_cpt) (finish_cpt hc₂)
    exact h
  have htrans : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) transformed :=
    cpt_comp (cpt_pair cpt_id hflip) run_cpt
  have htime : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool answer := by
    have h₂ := cpt_bitFlag (cpt_comp compile_cpt hc₂)
    have hH := cpt_bitFlag (cpt_comp htrans hcH)
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const [true])
      (cpt_sel h₂ (cpt_const [true]) (cpt_sel hH (cpt_const [true]) (cpt_const [])))) cpt_isEmpty
    exact h
  have ha (x : List Bool) : answer x = true ↔
      wfB x = true ∧ query₂ x = true ∧ queryH x = true := by
    cases h : wfB x <;> cases h₂ : query₂ x <;> cases hH : queryH x <;>
      simp [answer, sel, bflag, h, h₂, hH]
  have hquery₂ (φ : CNF) : query₂ (encodeCNF φ) = true ↔ Satisfiable (pairCNF φ) := by
    unfold query₂
    rw [compile_enc]
    exact (hd₂ _).symm.trans (pair_membership φ)
  have hqueryH (φ : CNF) (hs : Satisfiable (pairCNF φ)) :
      queryH (encodeCNF φ) = true ↔ Satisfiable φ := by
    obtain ⟨v, hv, hsat⟩ := solve dec₂ hd₂ (pairCNF φ) φ (pairCNF_two φ) hs (pair_vars φ)
    have he : flipNames (encodeCNF φ) = PEqualNP.Outside.CnfRestrictionSemantics.names v := by
      unfold flipNames
      rw [compile_enc, hv]
    have htrans_eq : transformed (encodeCNF φ) = encodeCNF (rename (flips v) φ) := by
      unfold transformed
      rw [he, run_enc]
    have hHorn_form := (pairCNF_correct (flips v) φ).mp hsat
    unfold queryH
    rw [htrans_eq]
    exact (hdH _).symm.trans ((hHorn _ hHorn_form).trans (sat_rename _ _))
  refine ⟨answer, ?_, htime⟩
  intro x
  rw [ha]
  constructor
  · rintro ⟨φ, rfl, hs, hn⟩
    have hp := (renamable_iff φ).mpr hn
    exact ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, (hquery₂ φ).mpr hp, (hqueryH φ hp).mpr hs⟩
  · rintro ⟨hw, h₂, hH⟩
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp hw
    have hp := (hquery₂ φ).mp h₂
    exact ⟨φ, rfl, (hqueryH φ hp).mp hH, (renamable_iff φ).mp hp⟩
