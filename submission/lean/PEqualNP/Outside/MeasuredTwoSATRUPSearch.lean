import PEqualNP.Outside.TwoSATShortRUP
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Library.SearchHelpers PEqualNP.Search

private abbrev Raw := List Bool

private def emptyMark (p : Raw × Raw) : Raw := sel (hd p.2) [true] []

private theorem emptyMark_cpt : ComputableInPolyTime encodePair (fun x : Raw => x) emptyMark := by
  change ComputableInPolyTime _ _ (fun p : Raw × Raw => sel (hd p.2) [true] [])
  have h := cpt_sel (cpt_hd1 cpt_unpairB2) (cpt_const [true]) (cpt_const [])
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

private theorem hasEmpty :
    ∃ flag : Raw → Raw, ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) flag ∧
      ∀ φ : CNF, flag (encodeCNF φ) ≠ [] ↔ [] ∈ φ := by
  obtain ⟨scan,hs,he⟩ := MeasuredClauseMap emptyMark emptyMark_cpt
  refine ⟨fun w => scan ([],w),cpt_comp (cpt_pair (cpt_const []) cpt_id) hs,fun φ => ?_⟩
  have hh (c : Clause) : emptyMark ([],encodeClause c) ≠ [] ↔ c = [] := by
    cases c with
    | nil => decide
    | cons l c =>
        have he : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
        rw [he,encodeLiteral_eq]
        simp [emptyMark,hd,sel]
  simp only [he,ne_eq,List.flatMap_eq_nil_iff]
  classical
  push Not
  constructor
  · rintro ⟨c,hc,h⟩
    exact (hh c).mp h ▸ hc
  · exact fun h => ⟨[],h,(hh []).mpr rfl⟩

private def mark (p : Raw × Raw) : Raw := sel (bflag (badI p.1 p.2)) [] p.2

private theorem mark_cpt : ComputableInPolyTime encodePair (fun x : Raw => x) mark := by
  change ComputableInPolyTime _ _ (fun p : Raw × Raw => sel (bflag (badI p.1 p.2)) [] p.2)
  have h := cpt_sel (cpt_badI cpt_unpairB1 cpt_unpairB2) (cpt_const []) cpt_unpairB2
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

private theorem flatmap_filter (f : Literal → Bool) (c : Clause) :
    c.flatMap (fun l => if f l then encodeLiteral l else []) = (c.filter f).flatMap encodeLiteral := by
  induction c with
  | nil => rfl
  | cons a c ih => cases h : f a <;> simp [h,ih]

private def badOccurrences (φ : CNF) : List Literal :=
  φ.flatMap (fun c => c.filter (fun l => badI (encodeCNF φ) (encodeLiteral l)))

private theorem badList :
    ∃ scan : Raw → Raw, ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) scan ∧
      ∀ φ : CNF, scan (encodeCNF φ) = (badOccurrences φ).flatMap encodeLiteral := by
  obtain ⟨onLit,hl,hls⟩ := MeasuredLiteralMap mark mark_cpt
  obtain ⟨onClause,hc,hcs⟩ := MeasuredClauseMap onLit hl
  refine ⟨fun s => onClause (s,s),cpt_comp (cpt_pair cpt_id cpt_id) hc,fun φ => ?_⟩
  change onClause (encodeCNF φ,encodeCNF φ) = _
  rw [hcs,badOccurrences,List.flatMap_assoc]
  apply List.flatMap_congr
  intro c _
  rw [hls,← flatmap_filter]
  apply List.flatMap_congr
  intro l _
  unfold mark
  cases badI (encodeCNF φ) (encodeLiteral l) <;> rfl

private theorem bad_spec (φ : CNF) (hw : IsKCNF 2 φ) (he : [] ∉ φ) (l : Literal) :
    badI (encodeCNF φ) (encodeLiteral l) = true ↔ Reach φ l (neg l) ∧ Reach φ (neg l) l := by
  have hwidth (c : Clause) (hc : c ∈ φ) : c.length = 1 ∨ c.length = 2 := by
    have ht := hw c hc
    have hp : c.length ≠ 0 := fun h => he (List.length_eq_zero_iff.mp h ▸ hc)
    omega
  rw [badI_enc φ hwidth]
  constructor
  · exact fun ⟨h₁,h₂⟩ => ⟨clos_sound h₁,clos_sound h₂⟩
  · exact fun ⟨h₁,h₂⟩ => ⟨clos_complete (rounds_le φ) h₁,clos_complete (rounds_le φ) h₂⟩

private def emit (w : Raw) : Raw := [false,false] ++ negI w ++ [false,false] ++ w ++ [false,false]

private theorem emit_cpt : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) emit :=
  cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 (cpt_const [false,false]) (cpt_negI cpt_id))
    (cpt_const [false,false])) cpt_id) (cpt_const [false,false])

private theorem emit_lit (l : Literal) : emit (encodeLiteral l) = encodeCNF [[],[neg l],[l]] := by
  simp [emit,negI_lit,encodeCNF,encodeClause,List.append_assoc]

/-- Produce an exact RUP refutation for every unsatisfiable width-two
canonical CNF, and the empty output for satisfiable instances. -/
theorem MeasuredTwoSATRUPSearch :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, IsKCNF 2 φ →
        (search (encodeCNF φ) = [] ↔ Satisfiable φ) ∧
        (¬Satisfiable φ → ∃ ρ : CNF,
          search (encodeCNF φ) = encodeCNF ρ ∧ ρ.length ≤ 3 ∧
          (encodeCNF ρ).length ≤ 2*(encodeCNF φ).length+6 ∧
          IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ) := by
  obtain ⟨empty,he,hes⟩ := hasEmpty
  obtain ⟨bad,hb,hbs⟩ := badList
  let search := fun s => sel (empty s) (sel (bad s) [] (emit (headI (bad s)))) (encodeCNF [[]])
  have hp : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) search :=
    cpt_sel he (cpt_sel hb (cpt_const []) (cpt_comp (cpt_comp hb cpt_headI) emit_cpt)) (cpt_const (encodeCNF [[]]))
  refine ⟨search,hp,fun φ hw => ?_⟩
  change (search (encodeCNF φ) = [] ↔ Satisfiable φ) ∧
    (¬Satisfiable φ → ∃ ρ : CNF, search (encodeCNF φ) = encodeCNF ρ ∧ ρ.length ≤ 3 ∧
      (encodeCNF ρ).length ≤ 2*(encodeCNF φ).length+6 ∧ IsRUPRun (clauseSet φ) (ρ.map List.toFinset) ∧ [] ∈ ρ)
  have finish (ρ : CNF) (hout : search (encodeCNF φ) = encodeCNF ρ)
      (hlen : ρ.length ≤ 3) (hsize : (encodeCNF ρ).length ≤ 2*(encodeCNF φ).length+6)
      (hvalid : IsRUPRun (clauseSet φ) (ρ.map List.toFinset)) (h0 : [] ∈ ρ) :
      (search (encodeCNF φ) = [] ↔ Satisfiable φ) ∧
        (¬Satisfiable φ → ∃ ρ : CNF, search (encodeCNF φ) = encodeCNF ρ ∧ ρ.length ≤ 3 ∧
          (encodeCNF ρ).length ≤ 2*(encodeCNF φ).length+6 ∧ IsRUPRun (clauseSet φ) (ρ.map List.toFinset) ∧ [] ∈ ρ) := by
    have hne : encodeCNF ρ ≠ [] := by
      intro h
      have e := encodeCNF_injective (h.trans (show [] = encodeCNF [] by rfl))
      simp [e] at h0
    exact ⟨hout ▸ iff_of_false hne (rup_run_refutes φ ρ hvalid h0),fun _ => ⟨ρ,hout,hlen,hsize,hvalid,h0⟩⟩
  by_cases h0 : [] ∈ φ
  · have hflag := (hes φ).mpr h0
    have hout : search (encodeCNF φ) = encodeCNF [[]] := by simp [search,sel,hflag]
    apply finish [[]] hout (by decide) _ (empty_rup h0) (by simp)
    have hsize : (encodeCNF ([[]] : CNF)).length = 2 := rfl
    omega
  · have hflag : empty (encodeCNF φ) = [] := by
      by_contra h
      exact h0 ((hes φ).mp h)
    cases hocc : badOccurrences φ with
    | nil =>
        have hb0 : bad (encodeCNF φ) = [] := by simp [hbs,hocc]
        have hs : Satisfiable φ := by
          by_contra hns
          obtain ⟨c,hc,l,hl,h₁,h₂⟩ := twoSat_conflict φ hw h0 hns
          have hmem : l ∈ badOccurrences φ :=
            List.mem_flatMap.mpr ⟨c,hc,List.mem_filter.mpr ⟨hl,(bad_spec φ hw h0 l).mpr ⟨h₁,h₂⟩⟩⟩
          simp [hocc] at hmem
        have he : search (encodeCNF φ) = [] := by simp [search,sel,hflag,hb0]
        exact ⟨iff_of_true he hs,fun h => (h hs).elim⟩
    | cons l ls =>
        have hi : bad (encodeCNF φ) = encodeLiteral l ++ ls.flatMap encodeLiteral := by
          rw [hbs,hocc,List.flatMap_cons]
        have hbad : encodeLiteral l ++ ls.flatMap encodeLiteral ≠ [] := by simp [encodeLiteral]
        have hout : search (encodeCNF φ) = encodeCNF [[],[neg l],[l]] := by
          simp [search,sel,hflag,hi,hbad,headI_lit,emit_lit]
        have hm : l ∈ badOccurrences φ := hocc.symm ▸ List.mem_cons_self
        obtain ⟨c,hc,h⟩ := List.mem_flatMap.mp hm
        obtain ⟨hl,hd⟩ := List.mem_filter.mp h
        obtain ⟨h₁,h₂⟩ := (bad_spec φ hw h0 l).mp hd
        apply finish [[],[neg l],[l]] hout (by simp) _ (conflict_trace l h₁ h₂) (by simp)
        rw [conflict_trace_size]
        have hs := in_formula_size φ c l hc hl
        omega

end PEqualNP.Outside
