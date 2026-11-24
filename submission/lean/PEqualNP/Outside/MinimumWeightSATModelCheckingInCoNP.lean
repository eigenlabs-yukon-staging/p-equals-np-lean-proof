import PEqualNP.Outside.ModelTrueCount
import PEqualNP.Outside.OptimalityVerificationCore
import PEqualNP.Library.SearchHelpers.SatVerifierCPT
import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.ModelWeightChecking

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.ModelTrueCount (Word modelWeight modelWeight_enc modelWeight_cpt)
open PEqualNP.Outside.AllFormulaNames (vars distinct)

abbrev ModelRel := Set (Word × Word)

def weight (φ : CNF) (σ : Assignment) : ℕ :=
  ((φ.flatMap fun c => c.map Prod.fst).toFinset.filter (fun i => σ i = true)).card

theorem weight_count (φ : CNF) (σ : Assignment) :
    ((distinct φ).filter σ).length = weight φ σ := by
  have hd : (distinct φ).Nodup := UniqueNameScan.scan_nodup [] _ (by simp)
  have he : (distinct φ).toFinset = (vars φ).toFinset := by
    ext i
    simp [distinct, UniqueNameScan.mem_scan]
  rw [← List.toFinset_card_of_nodup (hd.filter _), List.toFinset_filter, he]
  rfl

private def rawWeights (q : Word × Word) : Word × Word :=
  (modelWeight (q.1, (unpairB q.2).1), modelWeight (q.1, (unpairB q.2).2))

def lowerWeight : ModelRel :=
  {q | (rawWeights q).1.length < (rawWeights q).2.length}

private theorem rawWeights_cpt :
    ComputableInPolyTime encodePair encodePair rawWeights := by
  let f (q : Word × Word) := (unpairB q.2).1
  let g (q : Word × Word) := (unpairB q.2).2
  have hf : ComputableInPolyTime encodePair (fun x : Word => x) f :=
    cpt_comp (f := Prod.snd) (g := fun s : Word => (unpairB s).1) cpt_snd cpt_unpairB1
  have hg : ComputableInPolyTime encodePair (fun x : Word => x) g :=
    cpt_comp (f := Prod.snd) (g := fun s : Word => (unpairB s).2) cpt_snd cpt_unpairB2
  have hl₀ : ComputableInPolyTime encodePair encodePair
      (fun q : Word × Word => (q.1, f q)) :=
    cpt_pairG (f := Prod.fst) (g := f) cpt_fst hf
  have hr₀ : ComputableInPolyTime encodePair encodePair
      (fun q : Word × Word => (q.1, g q)) :=
    cpt_pairG (f := Prod.fst) (g := g) cpt_fst hg
  have hl := cpt_comp (g := modelWeight) hl₀ modelWeight_cpt
  have hr := cpt_comp (g := modelWeight) hr₀ modelWeight_cpt
  unfold rawWeights
  exact cpt_pairG hl hr

private def reverseLE (q : Word × Word) : Bool :=
  decide (q.2.length ≤ q.1.length)

private theorem reverseLE_cpt : ComputableInPolyTime encodePair Computability.encodeBool reverseLE :=
  LenCmp.lenLE_polyTime

private def strictWeight (q : Word × Word) : Bool := (bflag (reverseLE (rawWeights q))).isEmpty

private theorem strictWeight_cpt :
    ComputableInPolyTime encodePair Computability.encodeBool strictWeight := by
  have h := cpt_comp (f := rawWeights) (g := reverseLE) rawWeights_cpt reverseLE_cpt
  unfold strictWeight
  exact cpt_comp (g := List.isEmpty) (cpt_bitFlag h) cpt_isEmpty

theorem lowerWeight_cpt : DecidableInPolyTime encodePair lowerWeight := by
  refine ⟨strictWeight, ?_, strictWeight_cpt⟩
  intro q
  simp only [lowerWeight, Set.mem_setOf_eq]
  by_cases he : (rawWeights q).2.length ≤ (rawWeights q).1.length
  · simp [strictWeight, reverseLE, he, Nat.not_lt.mpr he, bflag]
  · simp [strictWeight, reverseLE, he, Nat.lt_of_not_ge he, bflag]

theorem lowerWeight_enc (φ : CNF) (a b : Word) :
    (encodeCNF φ, pairB a b) ∈ lowerWeight ↔ weight φ (asg a) < weight φ (asg b) := by
  simp only [lowerWeight, Set.mem_setOf_eq, rawWeights]
  rw [unpairB_pairB, modelWeight_enc, modelWeight_enc, un_length, un_length, weight_count, weight_count]

def feasibleModel : ModelRel := {q | SV q = true}

theorem sv_enc (φ : CNF) (w : Word) :
    (encodeCNF φ, w) ∈ feasibleModel ↔ CNF.eval (asg w) φ = true := by
  have hw : wfB (encodeCNF φ) = true := (wfB_iff _).mpr ⟨φ, rfl⟩
  change SV (encodeCNF φ, w) = true ↔ _
  simp [SV, hw, evalB_enc]

theorem weight_wit (φ : CNF) (σ : Assignment) : weight φ (asg (wit σ φ)) = weight φ σ := by
  unfold weight
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [wit, asg_codes, trueVars, List.mem_filter]
  have hm : i ∈ (φ.flatMap id).map Prod.fst := by
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map] at hi ⊢
    obtain ⟨c, hc, l, hl, he⟩ := hi
    exact ⟨l, ⟨c, hc, hl⟩, he⟩
  exact and_iff_right hm

theorem canonical_weight (L : Language Bool)
    (hL : ∀ x w : Word, pairB x w ∈ L ↔ w.length ≤ x.length ∧ (x, w) ∈ feasibleModel ∧
      ∀ v : Word, v.length ≤ x.length → (x, v) ∈ feasibleModel → (x, pairB v w) ∉ lowerWeight)
    (φ : CNF) (w : Word) :
    pairB (encodeCNF φ) w ∈ L ↔ w.length ≤ (encodeCNF φ).length ∧
      CNF.eval (asg w) φ = true ∧ ∀ σ : Assignment, CNF.eval σ φ = true → weight φ (asg w) ≤ weight φ σ := by
  refine (hL _ _).trans ?_
  constructor
  · rintro ⟨hsize, hf, hmin⟩
    refine ⟨hsize, (sv_enc φ w).mp hf, ?_⟩
    intro σ hs
    have hv : (encodeCNF φ, wit σ φ) ∈ feasibleModel := by
      apply (sv_enc φ _).mpr
      rwa [eval_wit]
    have hd := hmin _ (wit_length σ φ) hv
    have hl := (not_congr (lowerWeight_enc φ (wit σ φ) w)).mp hd
    rw [weight_wit, Nat.not_lt] at hl
    exact hl
  · rintro ⟨hsize, hf, hmin⟩
    refine ⟨hsize, (sv_enc φ w).mpr hf, ?_⟩
    intro v hv hsat hlt
    exact (Nat.not_lt.mpr (hmin (asg v) ((sv_enc φ v).mp hsat))) ((lowerWeight_enc φ v w).mp hlt)

end PEqualNP.Outside.ModelWeightChecking

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.ModelWeightChecking

theorem PEqualNP.Outside.MinimumWeightSATModelCheckingInCoNP :
    ∃ L : Language Bool, L ∈ coNP ∧
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
  have hspec (x w : List Bool) : pairB x w ∈ L ↔ w.length ≤ x.length ∧ (x, w) ∈ feasibleModel ∧
      ∀ v : List Bool, v.length ≤ x.length → (x, v) ∈ feasibleModel → (x, pairB v w) ∉ lowerWeight := by
    simpa only [Polynomial.eval_X, pairB, un] using hform x w
  refine ⟨L, hp, ?_⟩
  intro φ v
  change pairB (encodeCNF φ) (v.flatMap (fun i => (encodeLiteral (i, true)).drop 2)) ∈ L ↔ _
  have he : v.flatMap (fun i => (encodeLiteral (i, true)).drop 2) = v.flatMap vcode := by
    simp [encodeLiteral_eq]
  have hs : asg (v.flatMap vcode) = fun i => decide (i ∈ v) := by
    funext i
    rw [Bool.eq_iff_iff, asg_codes]
    simp
  rw [canonical_weight L hspec, he, hs]
  rfl
