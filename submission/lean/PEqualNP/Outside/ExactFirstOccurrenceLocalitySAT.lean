import PEqualNP.Outside.MeasuredFirstOccurrenceLocality
import PEqualNP.Outside.FirstOccurrenceEliminationWidth
import PEqualNP.Outside.MeasuredOccurrenceElimination
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard

/-- For each fixed first-occurrence radius, the exact language of
satisfiable canonical formulas meeting that syntactic radius is in P. -/
theorem ExactFirstOccurrenceLocalitySAT (k : ℕ) :
    {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧ Satisfiable φ ∧
      let order := φ.flatten.map Prod.fst
      ∀ c ∈ φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k} ∈ P := by
  obtain ⟨guard,hg,hgs⟩ := MeasuredFirstOccurrenceLocality k
  obtain ⟨run,hr,hrs⟩ := MeasuredOccurrenceElimination (2*(k+1))
  let flag := fun s => sel (bflag (wfB s)) [] (sel (bflag (guard s)) [] (bflag (decide (run s = [true]))))
  let accept := fun s => !(flag s).isEmpty
  have hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) flag :=
    cpt_sel cpt_wfF (cpt_const []) (cpt_sel (cpt_bitFlag hg) (cpt_const []) (cpt_eqF hr (cpt_const [true])))
  have hc : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool accept :=
    cpt_comp (g := fun s : List Bool => !s.isEmpty) hf bf_cpt_neL
  have ha (s : List Bool) : accept s = true ↔ wfB s = true ∧ guard s = true ∧ run s = [true] := by
    unfold accept flag
    by_cases h : run s = [true] <;> cases wfB s <;> cases guard s <;> simp [bflag,sel,h]
  refine ⟨accept,fun s => (show accept s = true ↔ _ from ?_).symm,hc⟩
  rw [ha]
  constructor
  · rintro ⟨hSyntax,hGuard,hRun⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff s).mp hSyntax
    have hLoc := (hgs φ).mp hGuard
    have hSat : Satisfiable φ := ((hrs φ).2.mp hRun).2
    exact ⟨φ,rfl,hSat,hLoc⟩
  · rintro ⟨φ,rfl,hSat,hLoc⟩
    let order := φ.flatten.map Prod.fst
    have hFin : ∀ c ∈ clauseSet φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k := by
      rintro c ⟨d,hd,rfl⟩ l hl m hm
      exact hLoc d hd l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm)
    have hWidth := FirstOccurrenceEliminationWidth k (clauseSet φ) order hFin (occurrence_order_covers φ)
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(hgs φ).mpr hLoc,(hrs φ).2.mpr ⟨hWidth,hSat⟩⟩

end PEqualNP.Outside
