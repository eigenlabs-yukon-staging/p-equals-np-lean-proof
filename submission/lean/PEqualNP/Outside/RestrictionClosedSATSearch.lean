import PEqualNP.Outside.RestrictionSearchSemantics
import PEqualNP.Outside.TrueNamesAsUnits

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Search
open PEqualNP.Outside.RestrictionSearchSemantics (solve)
open PEqualNP.Outside.TwoSatGreedyCore (finish finish_cpt)
open PEqualNP.Outside.TrueNamesAsUnits (emit emit_cpt emit_enc unitCNF)
open PEqualNP.Outside.HornRenameMachine (flips)

theorem PEqualNP.Outside.RestrictionClosedSATSearch
    (F : Set CNF) (L : Language Bool) (hP : L ∈ P)
    (hclosed : ∀ (ρ : ℕ → Option Bool) (φ : CNF), φ ∈ F →
      (φ.filterMap fun c =>
        if c.any (fun l => ρ l.1 == some l.2) then none
        else some (c.filter fun l => (ρ l.1).isNone)) ∈ F)
    (hcorrect : ∀ φ ∈ F, encodeCNF φ ∈ L ↔ Satisfiable φ) :
    ∃ find : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) find ∧
      ∀ φ ∈ F, Satisfiable φ →
        ∃ v : List ℕ,
          find (encodeCNF φ) = encodeCNF (v.map (fun i => [(i, true)])) ∧
          CNF.eval (fun i => decide (i ∈ v)) φ = true := by
  obtain ⟨dec, hd, ht⟩ := hP
  let find (x : List Bool) := emit (finish dec (x, x))
  have hfind : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) find := by
    have h := cpt_comp (cpt_comp (cpt_pair cpt_id cpt_id) (finish_cpt ht)) emit_cpt
    exact h
  have hc (φ : CNF) (hφ : φ ∈ F) : Satisfiable φ ↔ dec (encodeCNF φ) = true :=
    (hcorrect φ hφ).symm.trans (hd _)
  refine ⟨find, hfind, ?_⟩
  intro φ hφ hsat
  obtain ⟨v, hcode, hv⟩ := solve F hclosed dec hc φ φ hφ hsat (fun c hc l hl => ⟨c, hc, l, hl, rfl⟩)
  refine ⟨v, ?_, hv⟩
  change emit (finish dec (encodeCNF φ, encodeCNF φ)) = _
  rw [hcode, emit_enc]
  rfl
