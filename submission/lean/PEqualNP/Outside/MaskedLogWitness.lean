import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Outside.MeasuredMaskedFill

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

/-- Known uncertainty positions can be filled deterministically when their total search space
is polynomially bounded and the predicted fixed positions agree with some accepted witness. -/
theorem MaskedLogWitness
    (L : Language Bool) (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (mask word : List Bool → List Bool)
    (hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mask)
    (hw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) word)
    (q : Polynomial ℕ)
    (hbudget : ∀ x : List Bool, 2 ^ ((mask x).count true + 1) ≤ q.eval x.length)
    (complete : ∀ x : List Bool, x ∈ L → ∃ w : List Bool, (x, w) ∈ R ∧
      w.length = (mask x).length ∧
      ∀ i < (mask x).length, (mask x).getD i false = false → w.getD i false = (word x).getD i false)
    (sound : ∀ x w : List Bool, (x, w) ∈ R → x ∈ L) :
    L ∈ P := by
  obtain ⟨fill, hfill, hcalc⟩ := MeasuredMaskedFill
  let clock := fun x : List Bool => List.replicate (q.eval x.length) true
  let gen := fun z : List Bool × List Bool => fill (pairB (mask z.2) (word z.2), cand z.1.length)
  have hcand : ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x => cand x.length) :=
    cpt_iterGrow bf_cpt_succB 1 bf_succB_length cpt_id (cpt_const [])
  have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) gen :=
    cpt_comp (cpt_pairG (cpt_comp cpt_snd (cpt_pairB2 hm hw)) (cpt_comp (g := fun l : List Bool => cand l.length) cpt_fst hcand)) hfill
  have h := IndexedWitnessProjection R hR clock (L055 q) gen hg
  have heq : L =
      {x : List Bool | ∃ i < (clock x).length, (x, gen (List.replicate i true, x)) ∈ R} := by
    ext x
    change x ∈ L ↔ ∃ i < (clock x).length, (x, gen (List.replicate i true, x)) ∈ R
    constructor
    · intro hx
      obtain ⟨w, hw', hlen, hagree⟩ := complete x hx
      obtain ⟨seed, hlenSeed, hrecover⟩ := maskedSeed_exists (mask x) (word x) w hlen hagree
      refine ⟨idx seed, ?_, ?_⟩
      · have hidx := idx_bound seed
        have hb := hbudget x
        simp only [clock, List.length_replicate]
        rw [hlenSeed] at hidx
        omega
      · change (x, fill (pairB (mask x) (word x), cand (List.replicate (idx seed) true).length)) ∈ R
        rw [List.length_replicate, cand_idx]
        change (x, fill (List.replicate (mask x).length true ++ false :: (mask x ++ word x), seed)) ∈ R
        rwa [hcalc, hrecover]
    · rintro ⟨i, _, hi⟩
      exact sound x _ hi
  rwa [heq]

end PEqualNP.Outside
