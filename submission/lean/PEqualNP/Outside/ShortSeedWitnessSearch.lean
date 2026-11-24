import PEqualNP.Outside.LogWitnessCollapse

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

private theorem replaceWitness_polyTime {decode : List Bool × List Bool → List Bool}
    (hdecode : ComputableInPolyTime encodePair (fun x => x) decode) :
    ComputableInPolyTime encodePair encodePair
      (fun q : List Bool × List Bool => (q.1, decode q)) := by
  have hpacked : ComputableInPolyTime encodePair encodePair
      (fun q : List Bool × List Bool =>
        ((unpairB (pairB q.1 q.2)).1, decode (unpairB (pairB q.1 q.2)))) :=
    cpt_comp cpt_pairB (cpt_pair cpt_unpairB1 (cpt_comp cpt_unpairB hdecode))
  simpa [unpairB_pairB] using hpacked

/-- A logarithmic seed can describe a longer witness when the decoder is computable
in polynomial time on the reference tagged pair of the input and seed. -/
theorem ShortSeedWitnessSearch (L : Language Bool) (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (decode : List Bool × List Bool → List Bool)
    (hdecode : ComputableInPolyTime encodePair (fun y => y) decode)
    (k : Nat)
    (sound : ∀ x w : List Bool, (x, w) ∈ R → x ∈ L)
    (covers : ∀ x : List Bool, x ∈ L →
      ∃ s : List Bool, (x, decode (x, s)) ∈ R ∧ s.length ≤ k * (x.length + 1).log2) :
    L ∈ P := by
  let S : Set (List Bool × List Bool) := {q | (q.1, decode q) ∈ R}
  obtain ⟨verify, spec, hverify⟩ := hR
  have hS : DecidableInPolyTime encodePair S :=
    ⟨fun q => verify (q.1, decode q), fun q => spec (q.1, decode q),
      cpt_comp (replaceWitness_polyTime hdecode) hverify⟩
  refine LogWitnessCollapse L S hS k (fun x => ?_) covers
  exact ⟨fun hx => by obtain ⟨s, hs, _⟩ := covers x hx; exact ⟨s, hs⟩,
    fun ⟨s, hs⟩ => sound x (decode (x, s)) hs⟩

end PEqualNP.Outside
