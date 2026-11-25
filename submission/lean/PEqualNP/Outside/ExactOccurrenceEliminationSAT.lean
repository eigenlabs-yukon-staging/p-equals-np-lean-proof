import PEqualNP.Outside.MeasuredOccurrenceElimination
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.TwoSat

/-- Exact SAT in P for the canonical CNFs whose own occurrence order has
bounded intermediate elimination width, with no supplied order or universe. -/
theorem ExactOccurrenceEliminationSAT (k : ℕ) :
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧ Satisfiable φ ∧
      let order := φ.flatten.map Prod.fst
      ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl eliminate (clauses φ), Finset.card c ≤ k} ∈ P := by
  dsimp only
  obtain ⟨run,hr,hrs⟩ := MeasuredOccurrenceElimination k
  let flag := fun s => sel (bflag (wfB s)) [] (bflag (decide (run s = [true])))
  let accept := fun s => !(flag s).isEmpty
  have hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) flag :=
    cpt_sel cpt_wfF (cpt_const []) (cpt_eqF hr (cpt_const [true]))
  have hc : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool accept :=
    cpt_comp (g := fun s : List Bool => !s.isEmpty) hf bf_cpt_neL
  have ha (s : List Bool) : accept s = true ↔ wfB s = true ∧ run s = [true] := by
    unfold accept flag
    by_cases h : run s = [true] <;> cases wfB s <;> simp [h,sel,bflag]
  refine ⟨accept,fun s => (show accept s = true ↔ _ from ?_).symm,hc⟩
  rw [ha]
  constructor
  · rintro ⟨hSyntax,hResult⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff s).mp hSyntax
    obtain ⟨hWidth,hSat⟩ := (hrs φ).2.mp hResult
    exact ⟨φ,rfl,hSat,hWidth⟩
  · rintro ⟨φ,rfl,hSat,hWidth⟩
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(hrs φ).2.mpr ⟨hWidth,hSat⟩⟩

end PEqualNP.Outside
