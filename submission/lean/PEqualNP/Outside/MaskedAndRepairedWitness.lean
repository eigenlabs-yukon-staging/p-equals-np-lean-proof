import PEqualNP.Outside.BoundedRepairPairVerifier
import PEqualNP.Outside.MaskedLogWitness

namespace PEqualNP.Outside

open PEqualNP.Library

/-- Polynomial-time decision survives a logarithmic number of marked unknown bits together
with a fixed number of additional unmarked repairs. -/
theorem MaskedAndRepairedWitness
    (L : Language Bool) (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (mask word : List Bool → List Bool)
    (hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mask)
    (hw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) word)
    (q : Polynomial ℕ) (k : ℕ)
    (hbudget : ∀ x : List Bool, 2 ^ ((mask x).count true + 1) ≤ q.eval x.length)
    (complete : ∀ x : List Bool, x ∈ L → ∃ w : List Bool, w.length = (mask x).length ∧
      (∀ i < (mask x).length, (mask x).getD i false = false → w.getD i false = (word x).getD i false) ∧
      ∃ is : List ℕ, is.length = k ∧ (x, is.foldl (fun w i => w.modify i Bool.not) w) ∈ R)
    (sound : ∀ x w : List Bool, (x, w) ∈ R → x ∈ L) :
    L ∈ P := by
  have hrepair := BoundedRepairPairVerifier R hR k
  apply MaskedLogWitness L _ hrepair mask word hm hw q hbudget
  · intro x hx
    obtain ⟨w, hlen, hagree, is, hcount, hgood⟩ := complete x hx
    exact ⟨w, ⟨is, hcount, hgood⟩, hlen, hagree⟩
  · rintro x w ⟨is, _, hgood⟩
    exact sound x _ hgood

end PEqualNP.Outside
