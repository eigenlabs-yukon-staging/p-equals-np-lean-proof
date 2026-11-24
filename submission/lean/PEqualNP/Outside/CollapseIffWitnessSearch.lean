import PEqualNP.Outside.WitnessSearchOfCollapse
import PEqualNP.Library.L010

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

/-- P = NP exactly when all reference normal-form verifiers admit polynomial-time
production of accepted witnesses, with an explicit failure code. -/
theorem CollapseIffWitnessSearch :
    P = NP ↔
      ∀ (R : Set (List Bool × List Bool)), DecidableInPolyTime encodePair R →
        ∀ p : Polynomial Nat, (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) →
          ∃ f : List Bool → List Bool,
            ComputableInPolyTime (fun x => x) (fun x => x) f ∧
            ∀ x : List Bool,
              (f x = [] ∧ ∀ w : List Bool, (x, w) ∉ R) ∨
                ∃ w : List Bool, f x = true :: w ∧ (x, w) ∈ R := by
  constructor
  · intro h
    exact WitnessSearchOfCollapse (by rw [h])
  · intro h
    refine Set.Subset.antisymm L010 ?_
    intro L hL
    obtain ⟨R, p, hR, hb, hL_spec⟩ := L045 L hL
    obtain ⟨f, hf, hall⟩ := h R hR p hb
    let dec := fun x : List Bool => !(f x).isEmpty
    have hdec : ComputableInPolyTime (fun x => x) Computability.encodeBool dec :=
      cpt_comp (g := fun b => !b.isEmpty) hf bf_cpt_neL
    refine ⟨dec, fun x => ?_, hdec⟩
    refine (hL_spec x).trans ?_
    dsimp [dec]
    rcases hall x with ⟨hout, hno⟩ | ⟨w, hout, hw⟩
    · simp [hout, hno]
    · simp [hout, show ∃ w, (x, w) ∈ R from ⟨w, hw⟩]

end PEqualNP.Outside
