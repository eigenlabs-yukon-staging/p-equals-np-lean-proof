import PEqualNP.Outside.PrefixDecideHelpers
import PEqualNP.Outside.SatCodePrimitives
import PEqualNP.Library.L008
import PEqualNP.Library.Universal.Padding

namespace PEqualNP.Outside.OptimalityVerificationCore

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.PrefixDecideHelpers

private theorem cpt_and_flags {f g : Word × Word → Bool}
    (hf : ComputableInPolyTime encodePair Computability.encodeBool f)
    (hg : ComputableInPolyTime encodePair Computability.encodeBool g) :
    ComputableInPolyTime encodePair Computability.encodeBool (fun q => f q && g q) := by
  have hu := cpt_comp (cpt_pairG (cpt_bitFlag hf) (cpt_bitFlag hg)) cpt_pairB
  have htest := cpt_sel cpt_unpairB1 (cpt_const [true])
    (cpt_sel cpt_unpairB2 (cpt_const [true]) (cpt_const []))
  have h := cpt_comp (cpt_comp hu htest) cpt_isEmpty
  exact PEqualNP.Outside.SatCodePrimitives.cptl h (fun q => by
    cases f q <;> cases g q <;> simp [unpairB_pairB, sel])

def beats (C : Rel) (x u v : Word) : Prop := (x, pairB u v) ∈ C

def improves (R C : Rel) (p : Polynomial ℕ) : Language Bool :=
  {z | ∃ v : Word, good R p (unpairB z).1 v ∧ beats C (unpairB z).1 v (unpairB z).2}

theorem improves_np (R C : Rel) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (hC : DecidableInPolyTime encodePair C) :
    improves R C p ∈ NP := by
  obtain ⟨verify, hv, hvtime⟩ := hR
  obtain ⟨compare, hc, hctime⟩ := hC
  let B : Rel := {q | good R p (unpairB q.1).1 q.2 ∧
    beats C (unpairB q.1).1 q.2 (unpairB q.1).2}
  let goodTest (q : Word × Word) := decide (q.2.length ≤ p.eval (unpairB q.1).1.length) &&
    verify ((unpairB q.1).1, q.2)
  let cmp (q : Word × Word) := compare ((unpairB q.1).1, pairB q.2 (unpairB q.1).2)
  have hx := cpt_comp cpt_fst cpt_unpairB1
  have hw := cpt_comp cpt_fst cpt_unpairB2
  have hg : ComputableInPolyTime encodePair Computability.encodeBool goodTest := by
    have h := cpt_comp (cpt_pairG hx cpt_snd) (nf_decider verify p hvtime)
    exact h
  have hm : ComputableInPolyTime encodePair Computability.encodeBool cmp := by
    have hpair := cpt_comp (cpt_pairG cpt_snd hw) cpt_pairB
    have h := cpt_comp (cpt_pairG hx hpair) hctime
    exact h
  have hB : DecidableInPolyTime encodePair B := by
    refine ⟨fun q => goodTest q && cmp q, ?_, cpt_and_flags hg hm⟩
    intro q
    simp [B, goodTest, cmp, beats, good, hv, hc]
  refine ⟨B, p, hB, ?_⟩
  intro z
  change (∃ v, good R p (unpairB z).1 v ∧ beats C (unpairB z).1 v (unpairB z).2) ↔
    ∃ v, v.length ≤ p.eval z.length ∧ good R p (unpairB z).1 v ∧
      beats C (unpairB z).1 v (unpairB z).2
  constructor
  · rintro ⟨v, hgood, hb⟩
    have hz : (unpairB z).1.length ≤ z.length := by have h := unpairB_length z; omega
    exact ⟨v, hgood.1.trans (eval_mono_nat p hz), hgood, hb⟩
  · rintro ⟨v, _, hgood, hb⟩
    exact ⟨v, hgood, hb⟩

private theorem or_cpt {f g : Word × Word → Bool}
    (hf : ComputableInPolyTime encodePair Computability.encodeBool f)
    (hg : ComputableInPolyTime encodePair Computability.encodeBool g) :
    ComputableInPolyTime encodePair Computability.encodeBool (fun q => f q || g q) := by
  have hr := cpt_comp (cpt_pairG (cpt_bitFlag hf) (cpt_bitFlag hg)) cpt_pairB
  have ht := cpt_sel cpt_unpairB1 (cpt_sel cpt_unpairB2 (cpt_const [true]) (cpt_const []))
    (cpt_const [])
  have h := cpt_comp (cpt_comp hr ht) cpt_isEmpty
  exact PEqualNP.Outside.SatCodePrimitives.cptl h (fun q => by
    cases f q <;> cases g q <;> simp [unpairB_pairB, sel])

private theorem union_p_np (A B : Language Bool) (ha : A ∈ P) (hb : B ∈ NP) :
    ({x : Word | x ∈ A ∨ x ∈ B} : Language Bool) ∈ NP := by
  obtain ⟨da, hda, hca⟩ := ha
  obtain ⟨R, p, ⟨vr, hvr, hcr⟩, hs⟩ := hb
  let V : Rel := {q | q.1 ∈ A ∨ q ∈ R}
  have hV : DecidableInPolyTime encodePair V := by
    refine ⟨fun q => da q.1 || vr q, ?_, or_cpt (cpt_comp cpt_fst hca) hcr⟩
    intro q
    change (q.1 ∈ A ∨ q ∈ R) ↔ (da q.1 || vr q) = true
    refine (or_congr (hda q.1) (hvr q)).trans ?_
    simp
  refine ⟨V, p, hV, ?_⟩
  intro x
  constructor
  · intro h
    rcases h with ha | hb
    · exact ⟨[], by simp, Or.inl ha⟩
    · obtain ⟨w, hw, hr⟩ := (hs x).mp hb
      exact ⟨w, hw, Or.inr hr⟩
  · rintro ⟨w, hw, hmem⟩
    rcases hmem with ha | hr
    · exact Or.inl ha
    · exact Or.inr ((hs x).mpr ⟨w, hw, hr⟩)

private def goodLanguage (R : Rel) (p : Polynomial ℕ) : Language Bool :=
  {z | good R p (unpairB z).1 (unpairB z).2}

private def optLanguage (R C : Rel) (p : Polynomial ℕ) : Language Bool :=
  {z | z ∈ goodLanguage R p ∧ z ∉ improves R C p}

private theorem goodLanguage_p (R : Rel) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) : goodLanguage R p ∈ P := by
  obtain ⟨verify, h, hc⟩ := hR
  refine ⟨_, ?_, cpt_test verify p hc⟩
  intro z
  simp [goodLanguage, good, h]

private theorem coNP_bound (R C : Rel) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (hC : DecidableInPolyTime encodePair C) :
    optLanguage R C p ∈ coNP := by
  have hn := improves_np R C p hR hC
  have he : (optLanguage R C p)ᶜ =
      ({z : Word | z ∉ goodLanguage R p ∨ z ∈ improves R C p} : Language Bool) := by
    ext z
    change ¬ (z ∈ goodLanguage R p ∧ z ∉ improves R C p) ↔
      z ∉ goodLanguage R p ∨ z ∈ improves R C p
    tauto
  change (optLanguage R C p)ᶜ ∈ NP
  rw [he]
  exact union_p_np _ _ (L008 _ (goodLanguage_p R p hR)) hn

private theorem canonical_spec (R C : Rel) (p : Polynomial ℕ) (x w : Word) :
    pairB x w ∈ optLanguage R C p ↔
      w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
      ∀ v : Word, v.length ≤ p.eval x.length → (x, v) ∈ R → (x, pairB v w) ∉ C := by
  have h : pairB x w ∉ improves R C p ↔
      ∀ v, good R p x v → ¬ beats C x v w := by
    change (¬ ∃ v, good R p (unpairB (pairB x w)).1 v ∧
      beats C (unpairB (pairB x w)).1 v (unpairB (pairB x w)).2) ↔ _
    simp [unpairB_pairB]
  change (good R p (unpairB (pairB x w)).1 (unpairB (pairB x w)).2 ∧ _) ↔ _
  simp only [unpairB_pairB, h]
  change ((w.length ≤ p.eval x.length ∧ (x, w) ∈ R) ∧
    ∀ v, (v.length ≤ p.eval x.length ∧ (x, v) ∈ R) → (x, pairB v w) ∉ C) ↔ _
  constructor
  · rintro ⟨⟨hw, hw'⟩, hh⟩
    exact ⟨hw, hw', fun v hv hv' => hh v ⟨hv, hv'⟩⟩
  · rintro ⟨hw, hw', hh⟩
    exact ⟨⟨hw, hw'⟩, fun v hv => hh v hv.1 hv.2⟩

theorem checkingInCoNP
    (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (hC : DecidableInPolyTime encodePair C) :
    ∃ L : Language Bool, L ∈ coNP ∧
      ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (x, List.replicate v.length true ++ false :: (v ++ w)) ∉ C :=
  ⟨optLanguage R C p, coNP_bound R C p hR hC, canonical_spec R C p⟩

end PEqualNP.Outside.OptimalityVerificationCore
