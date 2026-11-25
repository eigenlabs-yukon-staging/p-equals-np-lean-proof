import PEqualNP.Outside.RenamableHornUnitRefutation
import PEqualNP.Outside.MeasuredRUP

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search

/-- Produce the single empty learned clause for any unsatisfiable
renamable Horn input, using unit propagation with no computed renaming. -/
theorem MeasuredRenamableHornRUPSearch :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∃ r : Assignment, ∀ c ∈ φ,
        ((c.map (fun l => (l.1,xor l.2 (r l.1)))).filter (fun l => l.2)).length ≤ 1) →
        (search (encodeCNF φ) = [] ↔ Satisfiable φ) ∧
        (¬Satisfiable φ → search (encodeCNF φ) = encodeCNF [[]] ∧
          IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (([[]] : CNF).map List.toFinset)) := by
  classical
  obtain ⟨test,ht,hs⟩ := MeasuredRUP
  let check := fun x => test (x,encodeClause [])
  let search := fun x => if check x then encodeCNF [[]] else []
  have hc := cpt_bitFlag (cpt_comp (cpt_pair cpt_id (cpt_const (encodeClause []))) ht)
  have hm := cpt_sel hc (cpt_const []) (cpt_const (encodeCNF [[]]))
  have he : (fun x => sel (if check x then [true] else []) [] (encodeCNF [[]])) = search := by
    funext x
    unfold search
    cases check x <;> rfl
  rw [he] at hm
  refine ⟨search,hm,fun φ hg => ?_⟩
  have htest : check (encodeCNF φ) = true ↔ ¬ Satisfiable φ :=
    (hs φ []).trans (RenamableHornUnitRefutation φ hg).symm
  constructor
  · change (if check (encodeCNF φ) then encodeCNF [[]] else []) = [] ↔ Satisfiable φ
    cases hc : check (encodeCNF φ) with
    | false =>
        have hSat : Satisfiable φ := by
          by_contra hn
          have h := htest.mpr hn
          simp [hc] at h
        simp [hc,hSat]
    | true =>
        have hSat := htest.mp hc
        simp [hc,hSat,encodeCNF,encodeClause]
  · intro h
    have hv := htest.mpr h
    constructor
    · simp [search,hv]
    · change IsRUPRun (clauseSet φ) (([[]] : CNF).map List.toFinset)
      apply (rup_run_cons φ [] []).mpr
      have hu : IsRUP (clauseSet φ) ∅ := (RenamableHornUnitRefutation φ hg).mp h
      exact ⟨by simpa only [List.append_nil,List.toFinset_nil] using hu,.nil⟩

end PEqualNP.Outside
