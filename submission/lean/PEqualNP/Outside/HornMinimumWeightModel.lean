import PEqualNP.Outside.HornPropagationSemantics
import PEqualNP.Library.SearchHelpers.SatVerifierCPT

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.HornPropagationSemantics (simplify next state saturated_state residual_sat)
open PEqualNP.Outside.HornPropagationCore (endState endState_cpt)
open PEqualNP.Outside.PositiveClauseCollector (qualifies)
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.PartialAssignmentFacts (retained_clause)
open PEqualNP.Outside.RestrictCnfHelpers (restrict merged eval_restrict)

private theorem least_model_sat (φ : CNF) (k : List ℕ)
    (hHorn : ∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1)
    (hu : next φ k = none) (σ : Assignment)
    (hfeasible : CNF.eval σ (simplify φ k) = true) :
    CNF.eval (fun i => decide (i ∈ k)) φ = true := by
  let a : Assignment := fun _ => false
  have ha : CNF.eval a (simplify φ k) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    apply List.any_eq_true.mpr
    by_cases allPositive : ∀ l ∈ c, l.2 = true
    · obtain ⟨parent, hp, he⟩ := retained_clause (show c ∈ restrict _ φ from hc)
      have hall : c.filter Prod.snd = c := List.filter_eq_self.mpr allPositive
      have hsub : (c.filter Prod.snd).Sublist (parent.filter Prod.snd) := by
        apply List.Sublist.filter
        rw [he]
        exact List.filter_sublist
      have hlen : c.length ≤ 1 := hall ▸ hsub.length_le.trans (hHorn parent hp)
      have hne : c ≠ [] := by
        intro isempty
        have he := List.all_eq_true.mp hfeasible c hc
        simp [isempty, Clause.eval] at he
      have hn := List.length_pos_iff.mpr hne
      have hexact : c.length = 1 := by omega
      have hnone := List.find?_eq_none.mp hu c hc
      simp [qualifies, List.all_eq_true.mpr allPositive, hexact] at hnone
    · push Not at allPositive
      obtain ⟨l, hl, hneg⟩ := allPositive
      exact ⟨l, hl, by simp [Literal.eval, a, hneg]⟩
  have hm : merged (valueOf k k) a = fun i => decide (i ∈ k) := by
    funext i
    by_cases h : i ∈ k <;> simp [merged, valueOf, h, a]
  have he := eval_restrict (valueOf k k) a φ
  rw [hm] at he
  exact he ▸ ha

theorem PEqualNP.Outside.HornMinimumWeightModel :
    ∃ f : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ φ : CNF, (∀ c ∈ φ, (c.filter Prod.snd).length ≤ 1) → Satisfiable φ →
        ∃ v : List ℕ,
          f (encodeCNF φ) = v.flatMap (fun i => (encodeLiteral (i, true)).drop 2) ∧
          CNF.eval (fun i => decide (i ∈ v)) φ = true ∧
          ∀ σ : Assignment, CNF.eval σ φ = true →
            (∀ i ∈ v, σ i = true) ∧
            let s := (φ.flatMap fun c => c.map Prod.fst).toFinset
            (s.filter (fun i => i ∈ v)).card ≤ (s.filter (fun i => σ i = true)).card := by
  refine ⟨fun w => (unpairB (endState w)).2, cpt_comp (g := fun s : List Bool => (unpairB s).2) endState_cpt cpt_unpairB2, ?_⟩
  rintro φ hh ⟨σ, hs⟩
  obtain ⟨k, hu, he, hl⟩ := saturated_state φ
  refine ⟨k, ?_, least_model_sat φ k hh hu σ (residual_sat hs (hl σ hs)), ?_⟩
  · change (unpairB (endState (encodeCNF φ))).2 = _
    rw [he, state, unpairB_pairB]
    simp [names, encodeLiteral_eq]
  · intro τ ht
    refine ⟨hl τ ht, ?_⟩
    dsimp
    apply Finset.card_le_card
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hf, hv⟩
    exact Finset.mem_filter.mpr ⟨hf, hl τ ht i hv⟩
