import PEqualNP.Outside.HornPropagationSemantics
import PEqualNP.Library.Universal.Padding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.HornPropagationCore (obstruction obstruction_cpt)
open PEqualNP.Outside.HornPropagationSemantics
open PEqualNP.Outside.RestrictCnfHelpers (restrict sat_restrict_iff)
open PEqualNP.Outside.PartialAssignmentFacts (retained_clause)
open PEqualNP.Outside.PositiveClauseCollector (gather_enc pick qualifies result)

private theorem wfFlag_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem obstruction_empty (φ : CNF) (k : List ℕ)
    (h : PEqualNP.Outside.HornPropagationCore.endState (encodeCNF φ) = state φ k) :
    obstruction (encodeCNF φ) = [] ↔ pick false (simplify φ k) = none := by
  unfold obstruction
  rw [h, residual_state, gather_enc]
  cases hp : pick false (simplify φ k) <;> simp [result]

private theorem sat_if_no_positive (ψ : CNF) (h : pick false ψ = none) :
    Satisfiable ψ := by
  refine ⟨fun _ => false, ?_⟩
  apply List.all_eq_true.mpr
  intro c hc
  have hnot := List.find?_eq_none.mp h c hc
  apply List.any_eq_true.mpr
  have he : c.all Prod.snd = false := by simpa [qualifies] using hnot
  have hn : ¬ ∀ l ∈ c, l.2 = true := by
    intro hall
    rw [List.all_eq_true.mpr hall] at he
    contradiction
  push Not at hn
  obtain ⟨l, hl, hp⟩ := hn
  exact ⟨l, hl, by simp [Literal.eval, hp]⟩

private theorem no_positive_of_horn (φ : CNF) (k : List ℕ) (σ : Assignment)
    (hs : CNF.eval σ (simplify φ k) = true) (hu : next φ k = none)
    (horn : ∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1) :
    pick false (simplify φ k) = none := by
  cases h : pick false (simplify φ k) with
  | none => rfl
  | some c =>
    have hall : c.all Prod.snd = true := by
      simpa [qualifies] using List.find?_some (p := qualifies false) h
    have hc : c ∈ simplify φ k := List.mem_of_find?_eq_some h
    have hlen : c.length ≤ 1 := by
      obtain ⟨c₀, hm, hr⟩ := retained_clause (show c ∈ restrict _ φ from hc)
      have hf : c.filter Prod.snd = c := List.filter_eq_self.mpr (List.all_eq_true.mp hall)
      have hsub : (c.filter Prod.snd).Sublist (c₀.filter Prod.snd) := by
        apply List.Sublist.filter
        rw [hr]
        exact List.filter_sublist
      exact hf ▸ (hsub.length_le.trans (horn c₀ hm))
    have hne : c ≠ [] := by
      intro he
      have hv := List.all_eq_true.mp hs c hc
      simp [he, Clause.eval] at hv
    have hunit : c.length = 1 := by
      have hp := List.length_pos_iff.mpr hne
      omega
    have hn := List.find?_eq_none.mp hu c hc
    simp [qualifies, hall, hunit] at hn

theorem PEqualNP.Outside.HornSATSublanguageInP :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF, (∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1) →
        (encodeCNF φ ∈ L ↔ Satisfiable φ) := by
  let answer (x : List Bool) := (sel (bflag (wfB x)) [true] (obstruction x)).isEmpty
  let L : Language Bool := {x | answer x = true}
  have htime : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool answer := by
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const [true]) obstruction_cpt) cpt_isEmpty
    exact h
  have hanswer (x : List Bool) : x ∈ L ↔ wfB x = true ∧ obstruction x = [] := by
    change answer x = true ↔ _
    cases h : wfB x <;> simp [answer, h, bflag, sel]
  have hsound : ∀ x, x ∈ L → x ∈ SAT := by
    intro x hx
    obtain ⟨hw, ho⟩ := (hanswer x).mp hx
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp hw
    obtain ⟨k, _, he, _⟩ := saturated_state φ
    have hsat := sat_if_no_positive _ ((obstruction_empty φ k he).mp ho)
    obtain ⟨σ, hs, _⟩ := (sat_restrict_iff _ _).mp hsat
    exact ⟨φ, rfl, σ, hs⟩
  refine ⟨L, ⟨answer, fun _ => Iff.rfl, htime⟩, hsound, ?_⟩
  intro φ hh
  constructor
  · intro h
    obtain ⟨ψ, he, hs⟩ := hsound _ h
    rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
  · rintro ⟨σ, hs⟩
    obtain ⟨k, hu, he, hk⟩ := saturated_state φ
    apply (hanswer _).mpr
    exact ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, (obstruction_empty φ k he).mpr
      (no_positive_of_horn φ k σ (residual_sat hs (hk σ hs)) hu hh)⟩
