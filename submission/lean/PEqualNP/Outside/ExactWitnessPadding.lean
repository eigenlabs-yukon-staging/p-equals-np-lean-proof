import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "Verifier" => Word × Word → Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private def acceptsExact (v : Verifier) (p : Polynomial Nat) (q : Word × Word) : Bool :=
  decide (q.2.length = p.eval q.1.length) && v (q.1, (unpairB q.2).1)

private theorem acceptsExact_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat) :
    ComputableInPolyTime encodePair Computability.encodeBool (acceptsExact v p) := by
  have hx := cpt_unpairB1
  have hw := cpt_unpairB2
  have ha := cpt_comp hx (L055 p)
  have h₁ := cpt_bitFlag (cpt_comp (cpt_pair ha hw) LenCmp.lenLE_polyTime)
  have h₂ := cpt_bitFlag (cpt_comp (cpt_pair hw ha) LenCmp.lenLE_polyTime)
  have hb := cpt_bitFlag (cpt_comp (cpt_pair hx (cpt_unpairB1_1 hw)) hv)
  have hc := cpt_sel h₁ (cpt_const []) (cpt_sel h₂ (cpt_const []) hb)
  have h := cpt_comp cpt_pairB (cpt_comp hc bf_cpt_neL)
  apply bf_cptl h
  rintro ⟨x,w⟩
  change (!(sel _ [] (sel _ [] _)).isEmpty) = _
  simp only [unpairB_pairB]
  by_cases he : w.length = p.eval x.length
  · have hk : p.eval x.length = w.length := he.symm
    cases hyes : v (x,(unpairB w).1) <;>
      simp [acceptsExact, sel, bflag, he, hyes]
  · by_cases hl : w.length ≤ p.eval x.length
    · have hno : ¬p.eval x.length ≤ w.length := by omega
      simp [acceptsExact, sel, bflag, he, hl, hno]
    · simp [acceptsExact, sel, bflag, he, hl]

/-- Every pinned NP language admits a polynomial-time verifier all of whose accepted
witnesses have the same polynomial length at a given input length. -/
theorem ExactWitnessPadding (L : Language Bool) (hL : L ∈ NP) :
    ∃ (R : Set (Word × Word)) (p : Polynomial Nat),
      DecidableInPolyTime encodePair R ∧
      (∀ x w : Word, (x,w) ∈ R → w.length = p.eval x.length) ∧
      (∀ x : Word, x ∈ L ↔ ∃ w : Word, (x,w) ∈ R) := by
  obtain ⟨R, p, ⟨v, spec, hv⟩, hb, he⟩ := L045 L hL
  let cap : Polynomial Nat := Polynomial.C 2 * p + 1
  let E : Set (Word × Word) := {q | acceptsExact v cap q = true}
  refine ⟨E, cap, ⟨acceptsExact v cap, fun _ => Iff.rfl, acceptsExact_polyTime hv cap⟩,
    fun x w h => ?_, fun x => ?_⟩
  · change acceptsExact v cap (x,w) = true at h
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  · constructor
    · intro hx
      obtain ⟨w, hw⟩ := (he x).mp hx
      let data := pairB w (un (2 * (p.eval x.length - w.length)))
      have hlen : data.length = cap.eval x.length := by
        have h := hb x w hw
        simp [data, cap, pairB_length, un_length]
        omega
      have hverify : v (x,(unpairB data).1) = true := by
        simpa [data, unpairB_pairB] using (spec (x,w)).mp hw
      exact ⟨data, Bool.and_eq_true_iff.mpr ⟨decide_eq_true hlen, hverify⟩⟩
    · rintro ⟨w, hw⟩
      have ht : acceptsExact v cap (x,w) = true := hw
      exact (he x).mpr ⟨(unpairB w).1, (spec _).mpr (Bool.and_eq_true_iff.mp ht).2⟩

end PEqualNP.Outside
