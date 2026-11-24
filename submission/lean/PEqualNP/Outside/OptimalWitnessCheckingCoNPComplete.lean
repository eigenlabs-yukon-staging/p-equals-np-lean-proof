import PEqualNP.Outside.OptimalComparatorWitnessSearch
import PEqualNP.Library.L031
import PEqualNP.Library.L018
import PEqualNP.Library.SearchHelpers.TwoSatCPT

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.ComparatorWitnessHelpers (improves improves_np beats)

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

private def feasible : Rel := {q | q.2 = [true] ∨ q.2.head? = some false ∧ SV (q.1, q.2.tail) = true}

private def better : Rel := {q | (unpairB q.2).1.head? = some false ∧ (unpairB q.2).2.headD false = true}

private theorem feasible_cpt : DecidableInPolyTime encodePair feasible := by
  let f (z : Word) := (unpairB z).2
  let check (z : Word) :=
    (sel (bflag (decide (f z = [true])))
      (sel (f z) [true] (sel (bflag ((f z).headD false))
        (sel (bflag (SV ((unpairB z).1, (f z).tail))) [true] []) [true]))
      []).isEmpty
  let dec (q : Word × Word) := check (pairB q.1 q.2)
  have hF : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) f := cpt_unpairB2
  have hD := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF hF (cpt_const [true])
  have hfirst := cpt_comp hF PEqualNP.Outside.SatCodePrimitives.cpt_firstF
  have hSat := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 (cpt_tail1 hF)) cpt_SV)
  have hcheck : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool check := by
    have h := cpt_comp (cpt_sel hD (cpt_sel hF (cpt_const [true])
      (cpt_sel hfirst (cpt_sel hSat (cpt_const [true]) (cpt_const [])) (cpt_const [true])))
      (cpt_const [])) cpt_isEmpty
    exact h
  refine ⟨dec, ?_, cpt_comp cpt_pairB hcheck⟩
  rintro ⟨x, _ | ⟨b, w⟩⟩
  · simp [feasible, dec, check, f, unpairB_pairB, bflag, sel]
  · cases h : SV (x, w) <;> cases b <;> cases w <;>
      simp [feasible, dec, check, f, unpairB_pairB, bflag, sel, h]

private theorem better_cpt : DecidableInPolyTime encodePair better := by
  let check (z : Word) :=
    let a := (unpairB (unpairB z).2).1
    let b := (unpairB (unpairB z).2).2
    (sel a [true] (sel (bflag (a.headD false)) (sel (bflag (b.headD false)) [true] []) [true])).isEmpty
  let dec (q : Word × Word) := check (pairB q.1 q.2)
  have ha := cpt_unpairB1_1 cpt_unpairB2
  have hb := cpt_unpairB2_1 cpt_unpairB2
  have fa := cpt_comp ha PEqualNP.Outside.SatCodePrimitives.cpt_firstF
  have fb := cpt_comp hb PEqualNP.Outside.SatCodePrimitives.cpt_firstF
  have ht : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool check := by
    have h := cpt_comp (cpt_sel ha (cpt_const [true]) (cpt_sel fa
      (cpt_sel fb (cpt_const [true]) (cpt_const [])) (cpt_const [true]))) cpt_isEmpty
    exact h
  refine ⟨dec, ?_, cpt_comp cpt_pairB ht⟩
  rintro ⟨x, z⟩
  cases h : (unpairB z).1 with
  | nil => simp [better, dec, check, unpairB_pairB, h, sel]
  | cons b w =>
    cases b <;> cases he : (unpairB z).2.headD false <;>
      simp [better, dec, check, unpairB_pairB, h, he, bflag, sel]

private theorem better_spec (x u v : Word) :
    beats better x u v ↔ u.head? = some false ∧ v.headD false = true := by
  simp [beats, better, unpairB_pairB]

private theorem better_order (x : Word) :
    (∀ u, ¬ beats better x u u) ∧
      (∀ u v t, beats better x u v → beats better x v t → beats better x u t) := by
  constructor
  · intro u hu
    have h := (better_spec x u u).mp hu
    cases u with
    | nil => simp at h
    | cons b us => cases b <;> simp_all
  · intro u v t huv hvt
    exact (better_spec x u t).mpr ⟨((better_spec x u v).mp huv).1, ((better_spec x v t).mp hvt).2⟩

private noncomputable def p : Polynomial ℕ := Polynomial.X + 1

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

theorem PEqualNP.Outside.OptimalWitnessCheckingInCoNPProof
    (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (hC : DecidableInPolyTime encodePair C) :
    ∃ L : Language Bool, L ∈ coNP ∧
      ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (x, List.replicate v.length true ++ false :: (v ++ w)) ∉ C :=
  ⟨optLanguage R C p, coNP_bound R C p hR hC, canonical_spec R C p⟩

private theorem dummy (x : Word) : pairB x [true] ∈ optLanguage feasible better p ↔ x ∉ SAT := by
  have hgood : good feasible p x [true] := by
    exact ⟨by simp [p], Or.inl rfl⟩
  have hImp : pairB x [true] ∈ improves feasible better p ↔ x ∈ SAT := by
    change (∃ v, good feasible p (unpairB (pairB x [true])).1 v ∧
      beats better (unpairB (pairB x [true])).1 v (unpairB (pairB x [true])).2) ↔ _
    simp only [unpairB_pairB]
    constructor
    · rintro ⟨v, hv, hc⟩
      have ht : v.head? = some false := by simpa [beats, better, unpairB_pairB] using hc
      obtain ⟨w, rfl⟩ : ∃ w, v = false :: w := by
        cases v with
        | nil => simp at ht
        | cons b w => cases b <;> simp_all
      have hb : w.length ≤ x.length := by simpa [p] using hv.1
      have hs : SV (x, w) = true := by simpa [feasible] using hv.2
      exact (SV_spec x).mpr ⟨w, hb, hs⟩
    · intro hs
      obtain ⟨w, hb, hv⟩ := (SV_spec x).mp hs
      refine ⟨false :: w, ⟨by simpa [p] using hb, ?_⟩, ?_⟩
      · exact Or.inr ⟨rfl, hv⟩
      · simp [beats, better, unpairB_pairB]
  change (good feasible p (unpairB (pairB x [true])).1 (unpairB (pairB x [true])).2 ∧
    pairB x [true] ∉ improves feasible better p) ↔ _
  simp only [unpairB_pairB, hgood, true_and]
  exact not_congr hImp

theorem PEqualNP.Outside.OptimalWitnessCheckingCoNPComplete :
    ∃ (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ) (L : Language Bool),
      DecidableInPolyTime encodePair R ∧ DecidableInPolyTime encodePair C ∧
      (∀ x : List Bool,
        let better := fun u v : List Bool =>
          (x, List.replicate u.length true ++ false :: (u ++ v)) ∈ C
        (∀ u, ¬ better u u) ∧
          (∀ u v t, better u v → better v t → better u t)) ∧
      L ∈ coNP ∧ (∀ A ∈ coNP, PolyTimeReducible A L) ∧
      ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (x, List.replicate v.length true ++ false :: (v ++ w)) ∉ C := by
  refine ⟨feasible, better, p, optLanguage feasible better p, feasible_cpt, better_cpt,
    better_order, coNP_bound feasible better p feasible_cpt better_cpt, ?_, canonical_spec feasible better p⟩
  · intro A hA
    obtain ⟨f, hf, hs⟩ := L031.2 Aᶜ hA
    refine ⟨fun x => pairB (f x) [true], cpt_pairB2 hf (cpt_const [true]), ?_⟩
    intro x
    have hnot : x ∈ A ↔ f x ∉ SAT := by
      have hh := not_congr (hs x)
      change (¬ x ∉ A) ↔ f x ∉ SAT at hh
      simpa only [Classical.not_not] using hh
    exact hnot.trans (dummy (f x)).symm

theorem PEqualNP.Outside.OptimalWitnessCheckingIffCollapseProof :
    P = NP ↔
    ∀ (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R → DecidableInPolyTime encodePair C →
      ∃ L : Language Bool, L ∈ P ∧ ∀ x w : List Bool,
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ p.eval x.length ∧ (x, w) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (x, List.replicate v.length true ++ false :: (v ++ w)) ∉ C := by
  constructor
  · intro he R C p hR hC
    have hp := coNP_bound R C p hR hC
    change (optLanguage R C p)ᶜ ∈ NP at hp
    rw [← he] at hp
    have hP := L008 _ hp
    rw [compl_compl] at hP
    exact ⟨optLanguage R C p, hP, canonical_spec R C p⟩
  · intro hh
    obtain ⟨L, hP, hspec⟩ := hh feasible better p feasible_cpt better_cpt
    have hred (x : Word) : pairB x [true] ∈ L ↔ x ∉ SAT :=
      (hspec x [true]).trans ((canonical_spec feasible better p x [true]).symm.trans (dummy x))
    have hSAT : SAT ∈ P := by
      obtain ⟨dec, hd, htime⟩ := L008 L hP
      let red (x : Word) := pairB x [true]
      have htime' : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) red :=
        cpt_pairB2 cpt_id (cpt_const [true])
      refine ⟨fun x => dec (red x), ?_, cpt_comp htime' htime⟩
      intro x
      have h : dec (red x) = true ↔ red x ∉ L := (hd _).symm
      have hz := not_congr (hred x)
      change red x ∉ L ↔ (¬ x ∉ SAT) at hz
      exact Classical.not_not.symm.trans (hz.symm.trans h.symm)
    exact (L018 SAT L031).mp hSAT
