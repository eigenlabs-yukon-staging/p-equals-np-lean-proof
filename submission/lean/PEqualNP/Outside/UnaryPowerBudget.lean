import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

/-- A unary exponent can be compared against a unary budget by halving the budget,
without ever constructing the exponentially long target. -/
theorem UnaryPowerBudget :
    DecidableInPolyTime encodePair
      {p : List Bool × List Bool | 2 ^ p.1.length ≤ p.2.length} := by
  let halve := fun p : List Bool × List Bool => half^[p.1.length] p.2
  have hi : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun s => half^[(unpairB s).1.length] (unpairB s).2) :=
    cpt_iterLen cpt_half' half_length_le cpt_unpairB1 cpt_unpairB2
  have hp := cpt_comp cpt_pairB hi
  have he : (fun p : List Bool × List Bool =>
    half^[(unpairB (pairB p.1 p.2)).1.length] (unpairB (pairB p.1 p.2)).2) = halve := by
    funext p
    simp only [unpairB_pairB, halve]
  rw [he] at hp
  refine ⟨fun p => !(halve p).isEmpty, fun p => ?_,
    cpt_comp (g := fun l : List Bool => !l.isEmpty) hp bf_cpt_neL⟩
  change 2 ^ p.1.length ≤ p.2.length ↔ (!(halve p).isEmpty) = true
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]
  change _ ↔ halve p ≠ []
  have hnonempty : halve p ≠ [] ↔ 0 < (halve p).length := by
    cases halve p <;> simp
  rw [hnonempty]
  change _ ↔ 0 < (half^[p.1.length] p.2).length
  rw [half_iter_length, Nat.div_pos_iff]
  exact ⟨fun h => ⟨by positivity, h⟩, fun h => h.2⟩

end PEqualNP.Outside
