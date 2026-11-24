import PEqualNP.Outside.VariableTruthTableSparseWitness
import PEqualNP.Library.L010

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

/-- A bounded truth-table reduction of a pinned NP-hard language to a sparse target
implies P = NP. The fixed collection of query coordinates and table entries are measured. -/
theorem VariableTruthTableSparseCollapse (A B : Language Bool) (hA : NPHard A)
    (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔
      T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    P = NP  := by
  refine Set.Subset.antisymm L010 ?_
  intro L hL
  obtain ⟨R,p,hR,bound,he⟩ := ExactWitnessPadding L hL
  obtain ⟨f,hf,hs⟩ :=
    VariableTruthTableSparseWitness R hR p bound A B hA s sparse k q hq T hT relation
  refine ⟨fun x => !(f x).isEmpty, fun x => ?_, cpt_comp (f := f) (g := fun l : Word => !l.isEmpty) hf bf_cpt_neL⟩
  refine (he x).trans ?_
  change (∃ w : Word, (x,w) ∈ R) ↔ (!(f x).isEmpty) = true
  rcases hs x with ⟨hf',hn⟩ | ⟨w,hf',hw,_⟩
  · simp only [hf', List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, iff_false]
    rintro ⟨w,hw⟩
    exact hn w hw
  · simp [hf', show ∃ u, (x,u) ∈ R from ⟨w,hw⟩]

end PEqualNP.Outside
