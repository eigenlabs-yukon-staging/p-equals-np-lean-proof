import PEqualNP.Library.L045
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private def disjoinVerifier (v : List Bool × List Bool → Bool)
    (p : List Bool × List Bool) : Bool :=
  v ((unpairB p.1).1, p.2) || v ((unpairB p.1).2, p.2)

private theorem disjoinVerifier_polyTime {v : List Bool × List Bool → Bool}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair Computability.encodeBool (disjoinVerifier v) := by
  have hleft : CPT (fun s => bflag (v ((unpairB (unpairB s).1).1, (unpairB s).2))) :=
    cpt_bitFlag (cpt_comp (cpt_pair (cpt_unpairB1_1 cpt_unpairB1) cpt_unpairB2) hv)
  have hright : CPT (fun s => bflag (v ((unpairB (unpairB s).1).2, (unpairB s).2))) :=
    cpt_bitFlag (cpt_comp (cpt_pair (cpt_unpairB2_1 cpt_unpairB1) cpt_unpairB2) hv)
  have h := cpt_comp cpt_pairB (cpt_comp (cpt_app2 hleft hright) bf_cpt_neL)
  apply bf_cptl h
  rintro ⟨q, w⟩
  simp only [unpairB_pairB, disjoinVerifier]
  cases v ((unpairB q).1, w) <;> cases v ((unpairB q).2, w) <;> rfl

private def orLanguage (A : Language Bool) : Language Bool :=
  {s | (unpairB s).1 ∈ A ∨ (unpairB s).2 ∈ A}

private theorem orLanguage_np (A : Language Bool) (hA : A ∈ NP) : orLanguage A ∈ NP := by
  obtain ⟨R, p, ⟨v, spec, hv⟩, bound, hSpec⟩ := L045 A hA
  refine ⟨{q | disjoinVerifier v q = true}, p,
    ⟨disjoinVerifier v, fun _ => Iff.rfl, disjoinVerifier_polyTime hv⟩, fun s => ?_⟩
  change ((unpairB s).1 ∈ A ∨ (unpairB s).2 ∈ A) ↔
    ∃ w : List Bool, w.length ≤ p.eval s.length ∧ disjoinVerifier v (s, w) = true
  have hlen := unpairB_length s
  have h₁ : (unpairB s).1.length ≤ s.length := by omega
  have h₂ : (unpairB s).2.length ≤ s.length := by omega
  constructor
  · intro h
    rcases h with ha | ha
    · obtain ⟨w, hw⟩ := (hSpec _).mp ha
      exact ⟨w, (bound _ _ hw).trans (eval_mono p h₁),
        Bool.or_eq_true_iff.mpr (Or.inl ((spec _).mp hw))⟩
    · obtain ⟨w, hw⟩ := (hSpec _).mp ha
      exact ⟨w, (bound _ _ hw).trans (eval_mono p h₂),
        Bool.or_eq_true_iff.mpr (Or.inr ((spec _).mp hw))⟩
  · rintro ⟨w, _, hw⟩
    rcases Bool.or_eq_true_iff.mp hw with e | e
    · exact Or.inl ((hSpec _).mpr ⟨w, (spec _).mpr e⟩)
    · exact Or.inr ((hSpec _).mpr ⟨w, (spec _).mpr e⟩)

/-- For every A in NP and every NP-hard target B, disjunction of two A queries can be
represented by one B query, in polynomial time on the pinned tagged pair encoding. -/
theorem DisjunctiveHardImage (A B : Language Bool) (hA : A ∈ NP) (hB : NPHard B) :
    ∃ f : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x => x) f ∧
      ∀ x y : List Bool, f (x, y) ∈ B ↔ x ∈ A ∨ y ∈ A := by
  obtain ⟨f, hc, spec⟩ := hB (orLanguage A) (orLanguage_np A hA)
  refine ⟨fun p => f (pairB p.1 p.2), cpt_comp cpt_pairB hc, fun x y => ?_⟩
  refine (spec (pairB x y)).symm.trans ?_
  change ((unpairB (pairB x y)).1 ∈ A ∨ (unpairB (pairB x y)).2 ∈ A) ↔ _
  simp [unpairB_pairB]

end PEqualNP.Outside
