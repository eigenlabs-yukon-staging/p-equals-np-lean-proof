import PEqualNP.Outside.RestrictionLexSearch
import PEqualNP.Outside.TrueNamesAsUnits

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Search
open PEqualNP.Outside.RestrictionLexSearch (solve LexLe)
open PEqualNP.Outside.TwoSatGreedyCore (finish finish_cpt)
open PEqualNP.Outside.TrueNamesAsUnits (emit emit_cpt emit_enc)
open PEqualNP.Outside.HornRenameMachine (flips)

theorem PEqualNP.Outside.RestrictionClosedLeastSATModel
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
          CNF.eval (fun i => decide (i ∈ v)) φ = true ∧
          ∀ σ : Assignment, CNF.eval σ φ = true →
            let bits := (φ.flatMap id).map (fun l => decide (l.1 ∈ v))
            let other := (φ.flatMap id).map (fun l => σ l.1)
            bits = other ∨ List.Lex (fun a b => a = false ∧ b = true) bits other := by
  obtain ⟨dec, hd, ht⟩ := hP
  let find (x : List Bool) := emit (finish dec (x, x))
  have hfind : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) find := by
    have h := cpt_comp (cpt_comp (cpt_pair cpt_id cpt_id) (finish_cpt ht)) emit_cpt
    exact h
  have hc (φ : CNF) (hφ : φ ∈ F) : Satisfiable φ ↔ dec (encodeCNF φ) = true :=
    (hcorrect φ hφ).symm.trans (hd _)
  refine ⟨find, hfind, ?_⟩
  intro φ hφ hsat
  obtain ⟨v, hcode, hv, hleast⟩ := solve F hclosed dec hc φ hφ hsat
  refine ⟨v, ?_, hv, hleast⟩
  change emit (finish dec (encodeCNF φ, encodeCNF φ)) = _
  rw [hcode, emit_enc]
  rfl
