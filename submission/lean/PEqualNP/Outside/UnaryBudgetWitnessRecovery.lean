import PEqualNP.Outside.PolynomialWitnessRecovery

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Universal

private theorem idx_fold (w : List Bool) :
    idx w = w.foldr (fun b j => (if b then 2 else 1) + 2 * j) 0 := by
  induction w with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [idx, ih]

/-- One polynomial-time machine, for each verifier, searches exactly the candidate
range specified by the length of the supplied clock word. On success it returns
the first accepting witness in the reference short-word-first enumeration. -/
theorem UnaryBudgetWitnessRecovery (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) :
    ∃ f : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x => x) f ∧
      ∀ x b : List Bool,
        let rank := fun w : List Bool => w.foldr (fun bit j => (if bit then 2 else 1) + 2 * j) 0
        (f (x,b) = [] ∧ ∀ w : List Bool, rank w < b.length → (x,w) ∉ R) ∨
          ∃ w : List Bool, rank w < b.length ∧ f (x,b) = true :: w ∧ (x,w) ∈ R ∧
            ∀ u : List Bool, rank u < rank w → (x,u) ∉ R := by
  obtain ⟨v, spec, hv⟩ := hR
  refine ⟨unaryRecovery v, unaryRecovery_polyTime hv, fun x b => ?_⟩
  simp only [← idx_fold]
  rcases unaryRecovery_spec v x b with ⟨hout, hnone⟩ | ⟨j, hj, hout, hyes, hfirst⟩
  · left
    refine ⟨hout, fun w hw hR => ?_⟩
    have hf := hnone (idx w) hw
    rw [cand_idx, (spec _).mp hR] at hf
    contradiction
  · right
    refine ⟨cand j, by simpa [idx_cand] using hj, hout, (spec _).mpr hyes,
      fun u hu hR => ?_⟩
    rw [idx_cand] at hu
    have hf := hfirst (idx u) hu
    rw [cand_idx, (spec _).mp hR] at hf
    contradiction

end PEqualNP.Outside
