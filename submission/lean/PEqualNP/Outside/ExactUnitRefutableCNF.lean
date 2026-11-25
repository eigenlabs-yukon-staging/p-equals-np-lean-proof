import PEqualNP.Outside.MeasuredRUP
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

/-- The exact canonical language refutable by unit propagation with no
initial assumptions belongs to the reference class P. -/
theorem ExactUnitRefutableCNF :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      IsRUP {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} ∅} ∈ P := by
  obtain ⟨test,ht,hs⟩ := MeasuredRUP
  let query := fun x => test (x,encodeClause [])
  let good := fun x => wfB x && query x
  have hq := cpt_bitFlag (cpt_comp (cpt_pair cpt_id (cpt_const (encodeClause []))) ht)
  have hm := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_sel cpt_wfF (cpt_const []) hq) bf_cpt_neL
  have he : (fun x => !(sel (bflag (wfB x)) [] (if query x then [true] else [])).isEmpty) = good := by
    funext x
    unfold good
    cases wfB x <;> cases query x <;> rfl
  rw [he] at hm
  refine ⟨good,fun x => ?_,hm⟩
  change (∃ φ : CNF, encodeCNF φ = x ∧ IsRUP (clauseSet φ) ∅) ↔ good x = true
  simp only [good,Bool.and_eq_true]
  have hq' (φ : CNF) : query (encodeCNF φ) = true ↔ IsRUP (clauseSet φ) ∅ := by
    exact hs φ []
  constructor
  · rintro ⟨φ,rfl,h⟩
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(hq' φ).mpr h⟩
  · rintro ⟨hw,h⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff _).mp hw
    exact ⟨φ,rfl,(hq' φ).mp h⟩

end PEqualNP.Outside
