import PEqualNP.Outside.BoundedBitRepair

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

/-- Testing a fixed number of repairs of a supplied word is itself a polynomial-time verifier. -/
theorem BoundedRepairPairVerifier
    (R : Set (List Bool × List Bool)) (hR : DecidableInPolyTime encodePair R) (k : ℕ) :
    DecidableInPolyTime encodePair
      {z : List Bool × List Bool | ∃ is : List ℕ, is.length = k ∧
        (z.1, is.foldl (fun word i => word.modify i Bool.not) z.2) ∈ R} := by
  let Q : Set (List Bool × List Bool) := {z | ((unpairB z.1).1, z.2) ∈ R}
  have hQ : DecidableInPolyTime encodePair Q := by
    obtain ⟨f, hf, hc⟩ := hR
    have hfirst : ComputableInPolyTime encodePair (fun x : List Bool => x)
        (fun z : List Bool × List Bool => (unpairB z.1).1) :=
      cpt_comp (f := fun z : List Bool × List Bool => z.1)
        (g := fun s => (unpairB s).1) cpt_fst cpt_unpairB1
    exact ⟨fun z => f ((unpairB z.1).1, z.2), fun z => hf _,
      cpt_comp (cpt_pairG hfirst cpt_snd) hc⟩
  obtain ⟨f, hf, hc⟩ := BoundedBitRepair Q hQ (fun s => (unpairB s).2) cpt_unpairB2 k
  refine ⟨fun z => f (pairB z.1 z.2), fun z => ?_, cpt_comp cpt_pairB hc⟩
  rw [← hf]
  change (∃ is : List ℕ, is.length = k ∧
    (z.1, is.foldl (fun word i => word.modify i Bool.not) z.2) ∈ R) ↔
    ∃ is : List ℕ, is.length = k ∧
      ((unpairB (pairB z.1 z.2)).1, is.foldl (fun word i => word.modify i Bool.not)
        (unpairB (pairB z.1 z.2)).2) ∈ R
  simp only [unpairB_pairB]

end PEqualNP.Outside
