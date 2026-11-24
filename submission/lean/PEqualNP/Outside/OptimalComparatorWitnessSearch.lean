import PEqualNP.Outside.EqualityIffWitnessSearch
import PEqualNP.Outside.SatCodePrimitives
import PEqualNP.Outside.BoundedEnumeration
import PEqualNP.Library.L008
import PEqualNP.Library.Universal.Padding

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding cand idx idx_lt_of_length_le cand_idx
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.BoundedEnumeration (idx idx_lt_of_length_le cand cand_idx)
open PEqualNP.Outside (EqualityIffWitnessSearch)

namespace PEqualNP.Outside.ComparatorWitnessHelpers

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

private theorem finite_minimum {α : Type} [DecidableEq α] (r : α → α → Prop)
    (hirr : ∀ x, ¬ r x x) (htrans : ∀ {x y z}, r x y → r y z → r x z) (s : Finset α) (hs : s.Nonempty) :
    ∃ w ∈ s, ∀ v ∈ s, ¬ r v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s hnot ih =>
    by_cases hb : s.Nonempty
    · obtain ⟨w, hw, hbest⟩ := ih hb
      by_cases ha : r a w
      · refine ⟨a, by simp, ?_⟩
        intro v hv hr
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hirr _ hr
        · exact hbest _ hv (htrans hr ha)
      · refine ⟨w, by simp [hw], ?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ha
        · exact hbest _ hv
    · have hnil : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      refine ⟨a, by simp, ?_⟩
      intro v hv
      have he : v = a := by simpa [hnil] using hv
      subst v
      exact hirr a

private theorem min_witness (R C : Rel) (p : Polynomial ℕ) (x : Word)
    (hirr : ∀ u, ¬ beats C x u u)
    (htrans : ∀ {u v t}, beats C x u v → beats C x v t → beats C x u t)
    (hex : ∃ w, good R p x w) :
    ∃ w, good R p x w ∧ ∀ v, good R p x v → ¬ beats C x v w := by
  classical
  let all := (Finset.range (2 ^ (p.eval x.length + 1))).image cand
  let feasible := all.filter (good R p x)
  have he (w : Word) : w ∈ feasible ↔ good R p x w := by
    simp only [feasible, Finset.mem_filter]
    constructor
    · exact And.right
    · intro h
      refine ⟨Finset.mem_image.mpr ⟨idx w, ?_, cand_idx w⟩, h⟩
      exact Finset.mem_range.mpr (by have hh := idx_lt_of_length_le h.1; omega)
  obtain ⟨w, hw⟩ := hex
  obtain ⟨m, hm, hmin⟩ := finite_minimum (beats C x) hirr htrans feasible ⟨w, (he w).mpr hw⟩
  exact ⟨m, (he m).mp hm, fun v hv => hmin v ((he v).mpr hv)⟩

private def optimal (R C : Rel) (p : Polynomial ℕ) : Rel :=
  {q | good R p q.1 q.2 ∧ pairB q.1 q.2 ∉ improves R C p}

private theorem optimal_decidable (R C : Rel) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (hp : improves R C p ∈ P) :
    DecidableInPolyTime encodePair (optimal R C p) := by
  obtain ⟨verify, hv, ht⟩ := hR
  obtain ⟨dec, hd, hc⟩ := L008 (improves R C p) hp
  let f (q : Word × Word) := decide (q.2.length ≤ p.eval q.1.length) && verify q
  let g (q : Word × Word) := dec (pairB q.1 q.2)
  have hf : ComputableInPolyTime encodePair Computability.encodeBool f := nf_decider verify p ht
  have hg : ComputableInPolyTime encodePair Computability.encodeBool g := cpt_comp cpt_pairB hc
  refine ⟨fun q => f q && g q, ?_, cpt_and_flags hf hg⟩
  intro q
  have hdec : dec (pairB q.1 q.2) = true ↔ pairB q.1 q.2 ∉ improves R C p := (hd _).symm
  simp [optimal, f, g, good, hv, hdec]

end PEqualNP.Outside.ComparatorWitnessHelpers

open PEqualNP.Outside.ComparatorWitnessHelpers

theorem PEqualNP.Outside.OptimalComparatorWitnessSearch :
    P = NP ↔
    ∀ (R C : Set (List Bool × List Bool)) (p : Polynomial ℕ),
      DecidableInPolyTime encodePair R →
      DecidableInPolyTime encodePair C →
      let beats := fun (x u v : List Bool) =>
        (x, List.replicate u.length true ++ false :: (u ++ v)) ∈ C
      (∀ x, (∀ u, ¬ beats x u u) ∧
        (∀ {u v t}, beats x u v → beats x v t → beats x u t)) →
      ∃ select : List Bool → List Bool,
        ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) select ∧
        ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
          (select x).length ≤ p.eval x.length ∧ (x, select x) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R → ¬ beats x v (select x) := by
  constructor
  · intro he R C p hR hC
    dsimp only
    intro horder
    have hp := improves_np R C p hR hC
    rw [← he] at hp
    have hd := optimal_decidable R C p hR hp
    obtain ⟨select, ht, hsel⟩ := (EqualityIffWitnessSearch.mp he) (optimal R C p) p hd
    refine ⟨select, ht, ?_⟩
    intro x hex
    obtain ⟨w, hw, hm⟩ := min_witness R C p x (horder x).1 (horder x).2 hex
    have hnot : pairB x w ∉ improves R C p := by
      change ¬ ∃ v, good R p (unpairB (pairB x w)).1 v ∧
        beats C (unpairB (pairB x w)).1 v (unpairB (pairB x w)).2
      simp only [unpairB_pairB]
      rintro ⟨v, hv, hb⟩
      exact hm v hv hb
    have ha := hsel x ⟨w, hw.1, ⟨hw, hnot⟩⟩
    have hl : good R p x (select x) ∧ pairB x (select x) ∉ improves R C p := ha.2
    refine ⟨hl.1.1, hl.1.2, ?_⟩
    intro v hv hr hb
    apply hl.2
    change ∃ v, good R p (unpairB (pairB x (select x))).1 v ∧
      beats C (unpairB (pairB x (select x))).1 v (unpairB (pairB x (select x))).2
    simpa only [unpairB_pairB] using (show ∃ v, good R p x v ∧ beats C x v (select x) from
      ⟨v, ⟨hv, hr⟩, hb⟩)
  · intro h
    apply EqualityIffWitnessSearch.mpr
    intro R p hR
    have hfalse : ComputableInPolyTime encodePair Computability.encodeBool (fun _ : Word × Word => false) := by
      have ht := cpt_comp cpt_fst (cpt_const [true])
      exact cpt_comp ht cpt_isEmpty
    have hempty : DecidableInPolyTime encodePair (∅ : Rel) :=
      ⟨fun _ => false, by simp, hfalse⟩
    obtain ⟨select, htime, hs⟩ := h R ∅ p hR hempty (by simp)
    exact ⟨select, htime, fun x hx => ⟨(hs x hx).1, (hs x hx).2.1⟩⟩
