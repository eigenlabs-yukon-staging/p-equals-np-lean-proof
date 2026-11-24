import PEqualNP.Outside.SparsePatternWitnessVerifier
import PEqualNP.Outside.SparsePatternQueryBatch
import PEqualNP.Outside.QueryListAny

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SparsePatternWitnessVerifier (verify verify_cpt queries queries_np sound isolates_witness)
open PEqualNP.Outside.SparsePatternQueryBatch (produce produce_cpt produce_enc results includes)
open PEqualNP.Outside.NPWitnessIsolation (goodWords mem_goodWords)
open PEqualNP.Outside.QueryListAny (answer answer_cpt answer_enc)

theorem PEqualNP.Outside.SparsePromiseOracleDeterministicSimulation :
    ∀ (L : Language Bool) (R : Set (List Bool × List Bool)) (p : Polynomial ℕ) (c : ℕ),
      DecidableInPolyTime encodePair R →
      (∀ x, x ∈ L ↔ ∃ w, w.length ≤ p.eval x.length ∧ (x,w) ∈ R) →
      (∀ x, ∃ S : Finset (List Bool), S.card ≤ c + 1 ∧
        ∀ w, w ∈ S ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R) →
      ∃ (D : List Bool × List Bool → Bool) (K : Language Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        ∀ O : List Bool → Bool,
          ComputableInPolyTime (fun w : List Bool => w) Computability.encodeBool O →
          (∀ z, (∀ w, D (z,w) = false) → O z = false) →
          (∀ z, (∃! w, D (z,w) = true) → O z = true) →
          L ∈ P := by
  intro L R p c ⟨dec,hd,hc⟩ hL hsmall
  refine ⟨verify p dec, queries p dec, queries_np p dec hc, verify_cpt p dec hc, fun _ => Iff.rfl, ?_⟩
  intro O hO hzero hone
  let F (x : List Bool) := answer O (produce p c x)
  have hFT : ComputableInPolyTime (fun w : List Bool => w) Computability.encodeBool F := by
    unfold F
    exact cpt_comp (f := produce p c) (g := answer O) (produce_cpt p c) (answer_cpt O hO)
  have hF (x : List Bool) : F x = true ↔ ∃ z ∈ results p c x, O z = true := by
    unfold F
    rw [produce_enc, answer_enc]
  refine ⟨F, ?_, hFT⟩
  intro x
  rw [hF]
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := (hL x).mp hx
    have hm := (mem_goodWords R p x w).mpr hw
    obtain ⟨S, hS, hmem⟩ := hsmall x
    have he : goodWords R p x = S := by
      ext v
      exact (mem_goodWords R p x v).trans (hmem v).symm
    have hb : (goodWords R p x).card ≤ c + 1 := by rwa [he]
    obtain ⟨f, hf⟩ := isolates_witness R p dec hd x c hb w hm
    refine ⟨_, includes p c x f, hone _ ?_⟩
    exact ⟨w, (hf w).mpr rfl, fun v hv => (hf v).mp hv⟩
  · rintro ⟨z, hz, ho⟩
    obtain ⟨s, rfl⟩ := PEqualNP.Outside.SparsePatternQueryBatch.sound p c x z hz
    by_contra hno
    have he : ∀ w, verify p dec (pairB x s,w) = false := by
      intro w
      cases hw : verify p dec (pairB x s,w)
      · rfl
      · have hgood := sound R p dec hd x s w hw
        exact False.elim (hno ((hL x).mpr ⟨w,(mem_goodWords R p x w).mp hgood⟩))
    rw [hzero _ he] at ho
    contradiction
