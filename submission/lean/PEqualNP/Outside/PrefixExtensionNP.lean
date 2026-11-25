import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Machines.ReduceNP

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

/-- The total raw-word language of a verifier's extendible prefixes. -/
def prefixLanguage (R : Set (List Bool × List Bool)) : Language Bool :=
  {s | ∃ w : List Bool, ((unpairB s).1, (unpairB s).2 ++ w) ∈ R}

theorem prefixLanguage_mem_NP (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R)
    (hbound : ∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) :
    prefixLanguage R ∈ NP := by
  obtain ⟨f, hf, hc⟩ := hR
  let transform := fun z : List Bool × List Bool =>
    ((unpairB z.1).1, (unpairB z.1).2 ++ z.2)
  have hfirst := cpt_comp cpt_fst cpt_unpairB1
  have hpre := cpt_comp cpt_fst cpt_unpairB2
  have hsecond := cpt_comp (cpt_pairG hpre cpt_snd) cpt_append
  have htransform : ComputableInPolyTime encodePair encodePair transform :=
    cpt_pairG hfirst hsecond
  refine ⟨{z | transform z ∈ R}, p, ⟨fun z => f (transform z), fun z => hf _,
    cpt_comp htransform hc⟩, fun s => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    have hlen := unpairB_length s
    have hb := hbound (unpairB s).1 ((unpairB s).2 ++ w) hw
    have hm := eval_mono p (show (unpairB s).1.length ≤ s.length by omega)
    simp only [List.length_append] at hb
    omega
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-- Extendible prefixes of a bounded verifier form an NP language in the pinned model. -/
theorem PrefixExtensionNP (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R)
    (hbound : ∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) :
    ∃ L : Language Bool, L ∈ NP ∧ ∀ x u : List Bool,
      List.replicate x.length true ++ false :: (x ++ u) ∈ L ↔
      ∃ w : List Bool, (x, u ++ w) ∈ R := by
  refine ⟨prefixLanguage R, prefixLanguage_mem_NP R p hR hbound, fun x u => ?_⟩
  change (pairB x u ∈ prefixLanguage R) ↔ _
  change (∃ w : List Bool, ((unpairB (pairB x u)).1, (unpairB (pairB x u)).2 ++ w) ∈ R) ↔ _
  simp only [unpairB_pairB]

end PEqualNP.Outside
