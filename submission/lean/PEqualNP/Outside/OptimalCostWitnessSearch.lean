import PEqualNP.Outside.LeastPrefixSelection
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.Padding
import PEqualNP.Outside.CollapseFromWitnessSearch
import PEqualNP.Outside.P_subset_NP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.LeastPrefixSelection (LexLe pref_order remove_head)
open PEqualNP.Outside (P_subset_NP CollapseFromWitnessSearch)

private theorem lex_left {u v a b : Word} (h : u.length = v.length)
    (hlex : LexLe (u ++ a) (v ++ b)) : LexLe u v := by
  induction u generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    exact Or.inl hv.symm
  | cons x u ih =>
    obtain ⟨y, v, rfl⟩ := List.exists_cons_of_ne_nil
      (l := v) (by intro he; simp [he] at h)
    have he : u.length = v.length := by simpa using h
    change LexLe (x :: (u ++ a)) (y :: (v ++ b)) at hlex
    by_cases hxy : x = y
    · subst y
      rcases ih he (remove_head x hlex) with rfl | hl
      · exact Or.inl rfl
      · exact Or.inr (List.Lex.cons hl)
    · rcases hlex with hword | hword
      · exact False.elim (hxy (List.cons.inj hword).1)
      · cases hword with
        | rel hr => exact Or.inr (List.Lex.rel hr)
        | cons _ => exact False.elim (hxy rfl)

private theorem pair_score_order (u v a b : Word) (h : LexLe (pairB u a) (pairB v b)) :
    u.length < v.length ∨ u.length = v.length ∧ LexLe u v := by
  rcases pref_order u.length v.length (u ++ a) (v ++ b)
    (by simpa [pairB, un, List.append_assoc] using h) with hlt | ⟨he, hl⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨he, lex_left he hl⟩

private def scoreRelation (R : Rel) (p : Polynomial ℕ) (cost : Word × Word → Word) : Rel :=
  {q | let w := (unpairB q.2).2
       q.2 = pairB (cost (q.1, w)) w ∧ good R p q.1 w}

private theorem score_decidable (R : Rel) (p : Polynomial ℕ) (cost : Word × Word → Word)
    (hR : DecidableInPolyTime encodePair R)
    (hcost : ComputableInPolyTime encodePair (fun x : Word => x) cost) :
    DecidableInPolyTime encodePair (scoreRelation R p cost) := by
  obtain ⟨verify, hv, hc⟩ := hR
  let verdict (z : Word) := decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)
  let packed (z : Word) := pairB (unpairB z).1 (unpairB (unpairB z).2).2
  let expected (z : Word) :=
    pairB (cost ((unpairB z).1, (unpairB (unpairB z).2).2)) (unpairB (unpairB z).2).2
  let check (z : Word) :=
    (sel (bflag (decide ((unpairB z).2 = expected z))) [true]
      (sel (bflag (verdict (packed z))) [true] [])).isEmpty
  let dec (q : Word × Word) := check (pairB q.1 q.2)
  have hval := cpt_unpairB2_1 cpt_unpairB2
  have htime := cpt_comp (cpt_pair cpt_unpairB1 hval) hcost
  have hE : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) expected := cpt_pairB2 htime hval
  have hEq := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF cpt_unpairB2 hE
  have hVer := cpt_bitFlag (cpt_comp (cpt_pairB2 cpt_unpairB1 hval) (cpt_test verify p hc))
  have hcheck : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool check := by
    have h := cpt_comp (cpt_sel hEq (cpt_const [true])
      (cpt_sel hVer (cpt_const [true]) (cpt_const []))) cpt_isEmpty
    exact h
  refine ⟨dec, ?_, cpt_comp cpt_pairB hcheck⟩
  rintro ⟨x, z⟩
  let w := (unpairB z).2
  change (z = pairB (cost (x, w)) w ∧ good R p x w) ↔ dec (x, z) = true
  by_cases he : z = pairB (cost (x, w)) w
  · have hv' : dec (x, z) = verdict (pairB x w) := by
      unfold dec check packed expected
      simp only [unpairB_pairB]
      change (sel (bflag (decide (z = pairB (cost (x, w)) w))) [true]
        (sel (bflag (verdict (pairB x w))) [true] [])).isEmpty = _
      rw [show decide (z = pairB (cost (x, w)) w) = true from decide_eq_true he]
      cases hv'' : verdict (pairB x w) <;> simp [hv'', bflag, sel]
    rw [hv']
    refine (and_iff_right he).trans ?_
    simp only [verdict, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq, good, hv]
  · have hv' : dec (x, z) = false := by
      unfold dec check packed expected
      simp only [unpairB_pairB]
      change (sel (bflag (decide (z = pairB (cost (x, w)) w))) [true] _).isEmpty = false
      simp [he, bflag, sel]
    simp [he, hv']

private theorem optimize (R : Rel) (p r : Polynomial ℕ) (cost : Word × Word → Word)
    (hR : DecidableInPolyTime encodePair R)
    (hc : ComputableInPolyTime encodePair (fun x : Word => x) cost)
    (hbound : ∀ x w, good R p x w → (cost (x, w)).length ≤ r.eval x.length)
    (he : extensions (scoreRelation R p cost) (Polynomial.C 2 * r + p + 1) ∈ P) :
    ∃ select : Word → Word,
      ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) select ∧
      ∀ x, (∃ w, good R p x w) → good R p x (select x) ∧
        ∀ v, good R p x v →
          (cost (x, select x)).length < (cost (x, v)).length ∨
          (cost (x, select x)).length = (cost (x, v)).length ∧ LexLe (cost (x, select x)) (cost (x, v)) := by
  let Q := Polynomial.C 2 * r + p + 1
  obtain ⟨s, hs, hselect⟩ := PEqualNP.Outside.LeastPrefixSelection.selector_of_extensions
    (scoreRelation R p cost) Q (score_decidable R p cost hR hc) he
  let select (x : Word) := (unpairB (s x)).2
  refine ⟨select, cpt_unpairB2_1 hs, ?_⟩
  intro x hex
  have hpad (v : Word) (h : good R p x v) : good (scoreRelation R p cost) Q x (pairB (cost (x, v)) v) := by
    have h₁ := h.1
    have h₂ := hbound x v h
    refine ⟨?_, ?_⟩
    · simp only [Q, pairB_length, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_one]
      omega
    · simp [scoreRelation, unpairB_pairB, h]
  obtain ⟨w, hw⟩ := hex
  obtain ⟨hgood, hleast⟩ := hselect x ⟨_, hpad w hw⟩
  have hg : s x = pairB (cost (x, select x)) (select x) ∧ good R p x (select x) := hgood.2
  refine ⟨hg.2, ?_⟩
  intro v hv
  have hl := hleast _ (hpad v hv)
  rw [hg.1] at hl
  exact pair_score_order _ _ _ _ hl

theorem PEqualNP.Outside.OptimalCostWitnessSearch :
    P = NP ↔
    ∀ (R : Set (List Bool × List Bool)) (p r : Polynomial ℕ)
      (cost : List Bool × List Bool → List Bool),
      DecidableInPolyTime encodePair R →
      ComputableInPolyTime encodePair (fun x : List Bool => x) cost →
      (∀ x w, w.length ≤ p.eval x.length → (x, w) ∈ R → (cost (x, w)).length ≤ r.eval x.length) →
      ∃ select : List Bool → List Bool,
        ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) select ∧
        ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
          (select x).length ≤ p.eval x.length ∧ (x, select x) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (cost (x, select x)).length < (cost (x, v)).length ∨
            (cost (x, select x)).length = (cost (x, v)).length ∧
              (cost (x, select x) = cost (x, v) ∨
                List.Lex (fun a b => a = false ∧ b = true) (cost (x, select x)) (cost (x, v))) := by
  constructor
  · intro equality R p r cost hR hcost hbound
    have he := extensions_np (scoreRelation R p cost) (Polynomial.C 2 * r + p + 1)
      (score_decidable R p cost hR hcost)
    rw [← equality] at he
    obtain ⟨select, hselect, hspec⟩ := optimize R p r cost hR hcost (fun x w h => hbound x w h.1 h.2) he
    refine ⟨select, hselect, ?_⟩
    intro x hx
    obtain ⟨hgood, hmin⟩ := hspec x hx
    exact ⟨hgood.1, hgood.2, fun v hle hm => hmin v ⟨hle, hm⟩⟩
  · intro hall
    apply Set.Subset.antisymm P_subset_NP
    apply CollapseFromWitnessSearch
    intro R p hR
    have ht : ComputableInPolyTime encodePair (fun x : Word => x) (fun _ : Word × Word => []) :=
      cpt_comp cpt_fst (cpt_const [])
    obtain ⟨select, hselect, hmin⟩ := hall R p 0 (fun _ => []) hR ht (by simp)
    exact ⟨select, hselect, fun x hx => ⟨(hmin x hx).1, (hmin x hx).2.1⟩⟩
