import PEqualNP.Outside.LexModelGateCompiler
import PEqualNP.Outside.LexModelCompareSemantics
import PEqualNP.Outside.OptimalityVerificationCore
import PEqualNP.Library.L031
import PEqualNP.Library.Universal.Padding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.LexModelGateFacts
open PEqualNP.Outside.LexModelGateCompiler (compile compile_cpt compile_enc)
open PEqualNP.Outside.LexModelCompareCore (output output_cpt)
open PEqualNP.Outside.LexModelCompareSemantics (compare_correct)
open PEqualNP.Outside.OptimalityVerificationCore (checkingInCoNP)

private abbrev Word := List Bool
private abbrev ModelRel := Set (Word × Word)

private def feasibleModel : ModelRel := {q | SV q = true}

private def lowerModel : ModelRel := {q | output q.1 q.2 = [true]}

private theorem lowerModel_cpt : DecidableInPolyTime encodePair lowerModel := by
  let f (z : Word) := output (unpairB z).1 (unpairB z).2
  let dec (q : Word × Word) :=
    (sel (bflag (decide (output q.1 q.2 = [true]))) [true] []).isEmpty
  have hf : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) f :=
    cpt_comp cpt_unpairB output_cpt
  have he := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF hf (cpt_const [true])
  have h := cpt_comp (cpt_sel he (cpt_const [true]) (cpt_const [])) cpt_isEmpty
  have ht : ComputableInPolyTime encodePair Computability.encodeBool dec :=
    PEqualNP.Outside.SatCodePrimitives.cptl (cpt_comp cpt_pairB h) (fun q => by simp [f, dec, unpairB_pairB])
  refine ⟨dec, ?_, ht⟩
  intro q
  by_cases h : output q.1 q.2 = [true] <;> simp [lowerModel, dec, sel, bflag, h]

private theorem sv_enc (φ : CNF) (w : Word) :
    SV (encodeCNF φ, w) = true ↔ CNF.eval (asg w) φ = true := by
  have hw : wfB (encodeCNF φ) = true := (wfB_iff _).mpr ⟨φ, rfl⟩
  simp [SV, hw, evalB_enc]

private theorem bits_wit (φ : CNF) (σ : Assignment) : bits (asg (wit σ φ)) φ = bits σ φ := by
  unfold bits
  apply List.map_congr_left
  intro l hl
  have hm : l.1 ∈ (φ.flatMap id).map Prod.fst := List.mem_map.mpr ⟨l, hl, rfl⟩
  rw [Bool.eq_iff_iff, wit, asg_codes, trueVars, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩

private theorem canonical (L : Language Bool)
    (hL : ∀ x w : Word, pairB x w ∈ L ↔ w.length ≤ x.length ∧ (x, w) ∈ feasibleModel ∧
      ∀ v : Word, v.length ≤ x.length → (x, v) ∈ feasibleModel → (x, pairB v w) ∉ lowerModel)
    (φ : CNF) (w : Word) :
    pairB (encodeCNF φ) w ∈ L ↔ w.length ≤ (encodeCNF φ).length ∧
      CNF.eval (asg w) φ = true ∧
      ∀ σ : Assignment, CNF.eval σ φ = true → ¬ List.Lex less (bits σ φ) (bits (asg w) φ) := by
  have hcmp (v : Word) :
      (encodeCNF φ, pairB v w) ∈ lowerModel ↔ List.Lex less (bits (asg v) φ) (bits (asg w) φ) :=
    compare_correct φ v w
  refine (hL _ _).trans ?_
  constructor
  · rintro ⟨hsize, hf, hmin⟩
    refine ⟨hsize, (sv_enc φ w).mp hf, ?_⟩
    intro σ hs hlt
    have hv : (encodeCNF φ, wit σ φ) ∈ feasibleModel := by
      change SV (encodeCNF φ, wit σ φ) = true
      apply (sv_enc φ _).mpr
      rwa [eval_wit]
    apply hmin _ (wit_length σ φ) hv
    apply (hcmp _).mpr
    rwa [bits_wit]
  · rintro ⟨hsize, hf, hmin⟩
    refine ⟨hsize, (sv_enc φ w).mpr hf, ?_⟩
    intro v hv hsat hlt
    exact hmin (asg v) ((sv_enc φ v).mp hsat) ((hcmp v).mp hlt)

private theorem wfFlag_cpt : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)
    (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem fallback_agrees : asg (vcode 0) = fallback := by
  funext i
  rw [Bool.eq_iff_iff]
  have h := asg_codes [0] i
  change asg (vcode 0) i = true ↔ i ∈ [0] at h
  exact h.trans (by simp [fallback])

private theorem false_cnf : ¬ Satisfiable ([[]] : CNF) := by
  rintro ⟨σ, hσ⟩
  simp [CNF.eval, Clause.eval] at hσ

theorem PEqualNP.Outside.LeastSATModelCheckingCoNPComplete :
    ∃ L : Language Bool, L ∈ coNP ∧ (∀ A ∈ coNP, PolyTimeReducible A L) ∧
      ∀ (φ : CNF) (names : List ℕ),
        let x := encodeCNF φ
        let w := names.flatMap (fun i => (encodeLiteral (i, true)).drop 2)
        let σ := fun i : ℕ => decide (i ∈ names)
        (List.replicate x.length true ++ false :: (x ++ w)) ∈ L ↔
          w.length ≤ x.length ∧ CNF.eval σ φ = true ∧
          ∀ τ : Assignment, CNF.eval τ φ = true →
            ¬ List.Lex (fun a b => a = false ∧ b = true)
              ((φ.flatMap id).map (fun l => τ l.1)) ((φ.flatMap id).map (fun l => σ l.1)) := by
  obtain ⟨L, hp, hform⟩ := checkingInCoNP feasibleModel lowerModel Polynomial.X
    ⟨SV, fun _ => Iff.rfl, cpt_SV⟩ lowerModel_cpt
  have hspec (x w : Word) : pairB x w ∈ L ↔ w.length ≤ x.length ∧ (x, w) ∈ feasibleModel ∧
      ∀ v : Word, v.length ≤ x.length → (x, v) ∈ feasibleModel → (x, pairB v w) ∉ lowerModel := by
    simpa only [Polynomial.eval_X, pairB, un] using hform x w
  have hg (φ : CNF) : pairB (encodeCNF (gate φ)) (vcode 0) ∈ L ↔ ¬ Satisfiable φ := by
    rw [canonical L hspec, fallback_agrees, no_better_fallback_iff]
    have hb : (vcode 0).length ≤ (encodeCNF (gate φ)).length := by
      have hc : (vcode 0).length ≤ (encodeClause lead).length := by decide
      have he : encodeCNF (gate φ) = encodeClause lead ++
          encodeCNF (φ.map (fun c => (0, true) :: c.map shift)) := rfl
      rw [he, List.length_append]
      omega
    simp [hb, fallback_sat]
  let red (x : Word) := pairB
    (sel (bflag (wfB x)) (encodeCNF (gate ([[]] : CNF))) (compile x)) (vcode 0)
  have hred : ComputableInPolyTime (fun x : Word => x) (fun x : Word => x) red :=
    cpt_pairB2 (cpt_sel wfFlag_cpt (cpt_const (encodeCNF (gate ([[]] : CNF)))) compile_cpt) (cpt_const (vcode 0))
  have hr (x : Word) : red x ∈ L ↔ x ∉ SAT := by
    cases h : wfB x
    · have hn : x ∉ SAT := by
        rintro ⟨φ, hf, _⟩
        have he := (wfB_iff _).mpr ⟨φ, hf⟩
        rw [h] at he
        contradiction
      simpa [red, sel, bflag, h, hn, false_cnf] using hg ([[]] : CNF)
    · obtain ⟨φ, rfl⟩ := (wfB_iff _).mp h
      have hs : encodeCNF φ ∈ SAT ↔ Satisfiable φ := by
        constructor
        · rintro ⟨ψ, he, hh⟩
          rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hh
        · exact fun h => ⟨φ, rfl, h⟩
      have he : red (encodeCNF φ) = pairB (encodeCNF (gate φ)) (vcode 0) := by
        simp [red, sel, bflag, h, compile_enc]
      exact he ▸ ((hg φ).trans (not_congr hs).symm)
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
    rw [canonical L hspec, he, hs]
    rfl
