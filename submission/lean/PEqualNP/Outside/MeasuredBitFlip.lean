import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.Ladner.Spec

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

private theorem modify_split (word : List Bool) (n : ℕ) :
    word.modify n Bool.not =
      word.take n ++ (match word.drop n with
        | [] => []
        | b :: rest => (!b) :: rest) := by
  induction word generalizing n with
  | nil => simp
  | cons b word ih =>
      cases n with
      | zero => rfl
      | succ n => exact congrArg (b :: ·) (ih n)

/-- Flip the bit at the unary index, leaving the word intact for out-of-range indices. -/
theorem MeasuredBitFlip :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.2.modify p.1.length Bool.not) := by
  let after := fun s => List.tail^[(unpairB s).1.length] (unpairB s).2
  have hafter : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) after :=
    cpt_iterLen cpt_tail (fun w => by simp) cpt_unpairB1 cpt_unpairB2
  have hbefore := cpt_tk cpt_unpairB1 cpt_unpairB2
  have hopposite := cpt_sel (cpt_hd1 hafter) (cpt_const [true]) (cpt_const [false])
  have hrest := cpt_sel hafter (cpt_const []) (cpt_app2 hopposite (cpt_tail1 hafter))
  have hflip := cpt_app2 hbefore hrest
  have hraw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2.modify (unpairB s).1.length Bool.not) := by
    refine cptE hflip (fun s => ?_)
    rw [tk_eq, modify_split]
    have hdrop : after s = (unpairB s).2.drop (unpairB s).1.length := by
      exact PEqualNP.Library.Ladner.iterate_tail _ _
    simp only [sel, hdrop]
    cases h : (unpairB s).2.drop (unpairB s).1.length with
    | nil => simp
    | cons b rest => cases b <;> simp [hd]
  have h := cpt_comp cpt_pairB hraw
  have he : (fun p : List Bool × List Bool =>
      (unpairB (pairB p.1 p.2)).2.modify (unpairB (pairB p.1 p.2)).1.length Bool.not) =
      (fun p : List Bool × List Bool => p.2.modify p.1.length Bool.not) := by
    funext p
    rw [unpairB_pairB]
  rwa [he] at h

end PEqualNP.Outside
