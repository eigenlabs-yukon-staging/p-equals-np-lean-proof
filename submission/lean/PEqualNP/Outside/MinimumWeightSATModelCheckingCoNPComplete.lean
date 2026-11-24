import PEqualNP.Outside.MinimumWeightModelGateCompiler
import PEqualNP.Library.L031

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.ModelWeightChecking
open PEqualNP.Outside.MinimumWeightModelGate (formula fallback fallback_sat minimum_iff)
open PEqualNP.Outside.MinimumWeightModelGateCompiler
  (compile compile_cpt compile_enc candidate candidate_cpt candidate_bound candidate_agrees
    eval_eq_of_agrees weight_eq_of_agrees)

private abbrev Word := List Bool

private theorem wfFlag_cpt : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)
    (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem emptyClause_unsat : ¬ Satisfiable ([[]] : CNF) := by
  rintro ⟨σ, hσ⟩
  simp [CNF.eval, Clause.eval] at hσ

theorem PEqualNP.Outside.MinimumWeightSATModelCheckingCoNPComplete :
    ∃ L : Language Bool, L ∈ coNP ∧ (∀ A ∈ coNP, PolyTimeReducible A L) ∧
      ∀ (φ : CNF) (names : List ℕ),
        let x := encodeCNF φ
        let w := names.flatMap (fun i => (encodeLiteral (i, true)).drop 2)
        let σ := fun i : ℕ => decide (i ∈ names)
        let W := fun (τ : Assignment) => ((φ.flatMap fun c => c.map Prod.fst).toFinset.filter
          (fun i => τ i = true)).card
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ x.length ∧ CNF.eval σ φ = true ∧
          ∀ τ : Assignment, CNF.eval τ φ = true → W σ ≤ W τ := by
  obtain ⟨L, hp, hform⟩ := PEqualNP.Outside.OptimalityVerificationCore.checkingInCoNP feasibleModel lowerWeight Polynomial.X
    ⟨SV, fun _ => Iff.rfl, cpt_SV⟩ lowerWeight_cpt
  have hspec (x w : Word) : pairB x w ∈ L ↔ w.length ≤ x.length ∧ (x, w) ∈ feasibleModel ∧
      ∀ v : Word, v.length ≤ x.length → (x, v) ∈ feasibleModel → (x, pairB v w) ∉ lowerWeight := by
    simpa only [Polynomial.eval_X, pairB, un] using hform x w
  let raw (x : Word) := pairB (compile x) (candidate x)
  have hpraw : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) raw :=
    cpt_pairB2 compile_cpt candidate_cpt
  have hg (φ : CNF) : raw (encodeCNF φ) ∈ L ↔ ¬ Satisfiable φ := by
    rw [show raw (encodeCNF φ) = pairB (encodeCNF (formula φ)) (candidate (encodeCNF φ)) by
      change pairB (compile (encodeCNF φ)) _ = _; rw [compile_enc], canonical_weight L hspec,
      eval_eq_of_agrees _ (candidate_agrees φ), weight_eq_of_agrees _ (candidate_agrees φ)]
    simp [candidate_bound, fallback_sat, minimum_iff]
  let red (x : Word) :=
    sel (bflag (wfB x)) (raw (encodeCNF ([[]] : CNF))) (raw x)
  have hred : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) red :=
    cpt_sel wfFlag_cpt (cpt_const (raw (encodeCNF ([[]] : CNF)))) hpraw
  have hr (x : Word) : red x ∈ L ↔ x ∉ SAT := by
    cases h : wfB x
    · have hn : x ∉ SAT := by
        rintro ⟨φ, hf, _⟩
        have he := (wfB_iff _).mpr ⟨φ, hf⟩
        rw [h] at he
        contradiction
      simpa [red, sel, bflag, h, hn, emptyClause_unsat] using hg ([[]] : CNF)
    · obtain ⟨φ, rfl⟩ := (wfB_iff _).mp h
      have hs : encodeCNF φ ∈ SAT ↔ Satisfiable φ := by
        constructor
        · rintro ⟨ψ, he, hh⟩
          rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hh
        · exact fun hh => ⟨φ, rfl, hh⟩
      simpa [red, h, bflag, sel] using (hg φ).trans (not_congr hs).symm
  refine ⟨L, hp, ?_, ?_⟩
  · intro A hA
    obtain ⟨f, hf, hspec⟩ := L031.2 Aᶜ hA
    refine ⟨fun x => red (f x), cpt_comp hf hred, ?_⟩
    intro x
    have h := not_congr (hspec x)
    change (¬ x ∉ A) ↔ f x ∉ SAT at h
    exact (Classical.not_not.symm.trans h).trans (hr (f x)).symm
  · intro φ v
    change pairB (encodeCNF φ) (v.flatMap (fun i => (encodeLiteral (i, true)).drop 2)) ∈ L ↔ _
    have he : v.flatMap (fun i => (encodeLiteral (i, true)).drop 2) = v.flatMap vcode := by
      simp [encodeLiteral_eq]
    have hs : asg (v.flatMap vcode) = fun i => decide (i ∈ v) := by
      funext i
      rw [Bool.eq_iff_iff, asg_codes]
      simp
    rw [canonical_weight L hspec, he, hs]
    rfl
