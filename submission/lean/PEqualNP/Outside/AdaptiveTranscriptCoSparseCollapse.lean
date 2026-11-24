import PEqualNP.Outside.AdaptiveTranscriptSparseCollapse

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool

private theorem branchFlip (answers leaf : Word → Bool) (d : Nat) (p : Word) :
    runSparseTranscript answers (fun w => !leaf w) d p = !(runSparseTranscript answers leaf d p) := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => exact ih (p ++ [answers p])

/-- A coNP-hard source with a fixed number of adaptive queries to a
cumulatively sparse target also entails the deterministic collapse. -/
theorem AdaptiveTranscriptCoSparseCollapse (A B : Language Bool)
    (hard : ∀ L ∈ coNP, PolyTimeReducible L A)
    (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (S : Finset Word),
      (∀ y ∈ S, y ∈ B ∧ y.length ≤ n) → S.card ≤ s.eval n)
    (d : Nat) (query : Word × Word → Word) (leaf : Word × Word → Bool)
    (hq : ComputableInPolyTime encodePair (fun x => x) query)
    (hl : ComputableInPolyTime encodePair Computability.encodeBool leaf)
    (correct : ∀ x : Word, x ∈ A ↔ runSparseTranscript
      (fun p => @decide (query (x,p) ∈ B) (Classical.propDecidable _))
      (fun p => leaf (x,p)) d [] = true) :
    P = NP := by
  have hardCompl : NPHard Aᶜ := by
    intro L hL
    have hc : Lᶜ ∈ coNP := by simpa [coNP] using hL
    obtain ⟨f, hf, hs⟩ := hard Lᶜ hc
    refine ⟨f, hf, fun x => ?_⟩
    have h := hs x
    change (x ∉ L) ↔ f x ∈ A at h
    change x ∈ L ↔ f x ∉ A
    simpa only [not_not] using not_congr h
  have flip : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime _ _ _ (fun b => some (!b)) (fun b => by cases b <;> rfl)
  apply AdaptiveTranscriptSparseCollapse Aᶜ B hardCompl s sparse d query
    (fun p => !leaf p) hq (cpt_comp hl flip)
  intro x
  let a := fun p => @decide (query (x,p) ∈ B) (Classical.propDecidable _)
  change (x ∉ A) ↔ runSparseTranscript a (fun p => !leaf (x,p)) d [] = true
  rw [branchFlip a (fun p => leaf (x,p)) d [], correct]
  change (runSparseTranscript a (fun p => leaf (x,p)) d [] ≠ true) ↔ _
  cases runSparseTranscript a (fun p => leaf (x,p)) d [] <;> simp

end PEqualNP.Outside
