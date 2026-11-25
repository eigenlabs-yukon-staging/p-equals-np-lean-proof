import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Outside.IndexedWitnessProjection

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

/-- If each positive input has an accepting witness formed by a polynomial-time
prefix and a suffix with a polynomial-size exhaustive search space, then the
language has a deterministic polynomial-time decider. -/
theorem LogarithmicSuffixWitnesses
    (L : Language Bool) (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R)
    (predict : List Bool → List Bool)
    (hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) predict)
    (q : Polynomial ℕ)
    (complete : ∀ x : List Bool, x ∈ L →
      ∃ s : List Bool, 2 ^ (s.length + 1) ≤ q.eval x.length ∧ (x, predict x ++ s) ∈ R)
    (sound : ∀ x s : List Bool, (x, predict x ++ s) ∈ R → x ∈ L) :
    L ∈ P := by
  let clock := fun x : List Bool => List.replicate (q.eval x.length) true
  let generate := fun p : List Bool × List Bool => predict p.2 ++ cand p.1.length
  have hcand : ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x => cand x.length) :=
    cpt_iterGrow bf_cpt_succB 1 bf_succB_length cpt_id (cpt_const [])
  have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) generate := by
    have hpre := cpt_comp cpt_snd hp
    have hsuf := cpt_comp cpt_fst hcand
    exact cpt_comp (cpt_pairG hpre hsuf) cpt_append
  have h := IndexedWitnessProjection R hR clock (L055 q) generate hg
  have heq : L =
      {x : List Bool | ∃ i < (clock x).length, (x, generate (List.replicate i true, x)) ∈ R} := by
    ext x
    change x ∈ L ↔ ∃ i < (clock x).length, (x, generate (List.replicate i true, x)) ∈ R
    constructor
    · intro hx
      obtain ⟨s, hbound, haccept⟩ := complete x hx
      refine ⟨idx s, ?_, ?_⟩
      · have hi := idx_bound s
        simp only [clock, List.length_replicate]
        omega
      · simpa [generate, cand_idx] using haccept
    · rintro ⟨i, _, hi⟩
      exact sound x _ hi
  rw [heq]
  exact h

end PEqualNP.Outside
