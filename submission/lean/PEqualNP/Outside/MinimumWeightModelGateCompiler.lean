import PEqualNP.Outside.MinimumWeightModelGate
import PEqualNP.Outside.LexModelGateCompiler

namespace PEqualNP.Outside.MinimumWeightModelGateCompiler

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Search
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.MinimumWeightModelGate (formula penalty guard)
open PEqualNP.Outside.AllFormulaNames (vars gather gather_enc gather_cpt)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def guardPrefix : Word := encodeLiteral (0, false) ++ [true, true, true, false, true, true]

def emitGuard (item : Word) : Word := guardPrefix ++ item ++ [false, false]

theorem emitGuard_enc (i : ℕ) : emitGuard (vcode i) = encodeClause (guard i) := by
  have hp : vcode (penalty i) = true :: false :: true :: true :: vcode i := by
    rw [penalty, vcode_bit false _ (by simp), vcode_bit true _ (by simp)]
  simp only [emitGuard, guardPrefix, MinimumWeightModelGate.guard, encodeClause, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]
  simp only [encodeLiteral_eq, Prod.fst, Prod.snd, hp]
  rfl

def emitPenalty (item : Word) : Word := true :: false :: true :: true :: item

theorem emitPenalty_enc (i : ℕ) : emitPenalty (vcode i) = vcode (penalty i) := by
  rw [penalty, vcode_bit false _ (by simp), vcode_bit true _ (by simp)]
  rfl

def emit (asClause : Bool) (item : Word) : Word :=
  if asClause then emitGuard item else emitPenalty item

theorem emit_cpt (asClause : Bool) : CPT (emit asClause) := by
  cases asClause
  · exact cpt_cons1 true (cpt_cons1 false (cpt_cons1 true (cpt_cons1 true cpt_id)))
  · exact cpt_app2 (cpt_app2 (cpt_const guardPrefix) cpt_id) (cpt_const [false, false])

theorem emit_length (asClause : Bool) (item : Word) :
    (emit asClause item).length ≤ item.length + 12 := by
  cases asClause <;> simp [emit, emitGuard, emitPenalty, guardPrefix, encodeLiteral_eq, vcode] <;> omega

def step (asClause : Bool) (z : Word) : Word :=
  let r := (unpairB z).1
  let a := (unpairB z).2
  sel r z (pairB (dropI r) (a ++ emit asClause (headI r)))

theorem step_cpt (asClause : Bool) : CPT (step asClause) := by
  have hr := cpt_unpairB1
  have hhead := cpt_comp hr cpt_headI
  have hout := cpt_app2 cpt_unpairB2 (cpt_comp (g := emit asClause) hhead (emit_cpt asClause))
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 (cpt_comp hr cpt_dropI) hout)) (fun _ => rfl)

theorem step_length (asClause : Bool) (z : Word) :
    (step asClause z).length ≤ z.length + 13 := by
  have h := unpairB_length z
  have hd := congrArg List.length (headI_dropI (unpairB z).1)
  have he := emit_length asClause (headI (unpairB z).1)
  simp only [List.length_append] at hd
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length, List.length_append]
    omega

def loop (asClause : Bool) (w : Word) : Word :=
  (unpairB ((step asClause)^[w.length] (pairB w []))).2

theorem loop_cpt (asClause : Bool) : CPT (loop asClause) := by
  obtain ⟨m⟩ := step_cpt asClause
  unfold loop
  exact cpt_comp (g := fun r : Word => (unpairB r).2) (cpt_comp (cpt_pair (cpt_pairB2 cpt_id (cpt_const [])) cpt_id)
    (Iter.iter_polyTime (step asClause) m 13 (step_length asClause))) cpt_unpairB2

theorem scan (asClause : Bool) (vs : List ℕ) (a : Word) :
    (step asClause)^[vs.length] (pairB (vs.flatMap vcode) a) =
      pairB [] (a ++ vs.flatMap (fun i => emit asClause (vcode i))) := by
  induction vs generalizing a with
  | nil => simp
  | cons v vs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : step asClause (pairB ((v :: vs).flatMap vcode) a) =
        pairB (vs.flatMap vcode) (a ++ emit asClause (vcode v)) := by
      simp [step, sel, unpairB_pairB, vcode_ne_nil, dropI_vcode, headI_vcode]
    rw [hs, ih, List.flatMap_cons, List.append_assoc]

theorem loop_enc (asClause : Bool) (vs : List ℕ) :
    loop asClause (vs.flatMap vcode) = vs.flatMap (fun i => emit asClause (vcode i)) := by
  have hlen := length_le_flatMap_vcode vs
  have hfix : step asClause (pairB [] (vs.flatMap (fun i => emit asClause (vcode i)))) =
      pairB [] (vs.flatMap (fun i => emit asClause (vcode i))) := by
    simp [step, sel, unpairB_pairB]
  unfold loop
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, scan, List.nil_append,
    Function.iterate_fixed hfix, unpairB_pairB]

def compile (w : Word) : Word := LexModelGateCompiler.compile w ++ loop true (gather w)

def candidate (w : Word) : Word := vcode 0 ++ loop false (gather w)

theorem compile_cpt : CPT compile := by
  exact cpt_app2 LexModelGateCompiler.compile_cpt (cpt_comp gather_cpt (loop_cpt true))

theorem candidate_cpt : CPT candidate := by
  exact cpt_app2 (cpt_const (vcode 0)) (cpt_comp gather_cpt (loop_cpt false))

theorem encode_append (φ ψ : CNF) :
    encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  exact List.flatMap_append

theorem guard_flatMap (vs : List ℕ) :
    vs.flatMap (fun i => emitGuard (vcode i)) = encodeCNF (vs.map guard) := by
  simp [emitGuard_enc, encodeCNF, List.flatMap_map, Function.comp_def]

theorem names_gather (φ : CNF) : gather (encodeCNF φ) = (vars φ).flatMap vcode := gather_enc φ

theorem compile_enc (φ : CNF) : compile (encodeCNF φ) = encodeCNF (formula φ) := by
  rw [compile, LexModelGateCompiler.compile_enc, names_gather, loop_enc]
  change _ ++ (vars φ).flatMap (fun i => emitGuard (vcode i)) = _
  rw [guard_flatMap, formula, encode_append]

def candidateNames (φ : CNF) : List ℕ := 0 :: (vars φ).map penalty

theorem candidate_enc (φ : CNF) :
    candidate (encodeCNF φ) = (candidateNames φ).flatMap vcode := by
  rw [candidate, names_gather, loop_enc]
  simp [emit, emitPenalty_enc, candidateNames, List.flatMap_map, Function.comp_def]

theorem penalty_lengths (vs : List ℕ) :
    ((vs.map penalty).flatMap vcode).length ≤ (encodeCNF (vs.map guard)).length := by
  induction vs with
  | nil => simp [encodeCNF]
  | cons i vs ih =>
    change (vcode (penalty i) ++ (vs.map penalty).flatMap vcode).length ≤
      (encodeClause (guard i) ++ encodeCNF (vs.map guard)).length
    simp only [List.length_append]
    have h : (vcode (penalty i)).length ≤ (encodeClause (guard i)).length := by
      simp [MinimumWeightModelGate.guard, encodeClause, encodeLiteral_eq] <;> omega
    omega

theorem candidate_bound (φ : CNF) :
    (candidate (encodeCNF φ)).length ≤ (encodeCNF (formula φ)).length := by
  rw [candidate_enc, formula, encode_append]
  simp only [candidateNames, List.flatMap_cons, List.length_append]
  have hl := penalty_lengths (vars φ)
  have hr : (vcode 0).length ≤ (encodeCNF (LexModelGateFacts.gate φ)).length := by
    change _ ≤ (encodeClause LexModelGateFacts.lead ++ _).length
    have hc : (vcode 0).length ≤ (encodeClause LexModelGateFacts.lead).length := by decide
    rw [List.length_append]
    omega
  omega

theorem candidate_agrees (φ : CNF) (i : ℕ) (hi : i ∈ vars (formula φ)) :
    asg (candidate (encodeCNF φ)) i = MinimumWeightModelGate.fallback i := by
  rw [candidate_enc, Bool.eq_iff_iff, asg_codes]
  simp only [candidateNames, List.mem_cons, List.mem_map, MinimumWeightModelGate.fallback,
    decide_eq_true_eq]
  rcases (MinimumWeightModelGate.mem_names φ i).mp hi with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · simp
  · have h₀ : 2 * j + 1 ≠ 0 := by omega
    have h₁ : (2 * j + 1) % 4 ≠ 2 := by omega
    simp only [h₀, h₁, false_or, iff_false]
    rintro ⟨k, _, h⟩
    rw [MinimumWeightModelGate.penalty_eq] at h
    omega
  · constructor
    · intro _
      right
      rw [MinimumWeightModelGate.penalty_eq]
      omega
    · exact fun _ => Or.inr ⟨j, hj, rfl⟩

theorem eval_eq_of_agrees (φ : CNF) {a b : Assignment}
    (h : ∀ i ∈ vars φ, a i = b i) : CNF.eval a φ = CNF.eval b φ := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNF.eval, List.all_eq_true, Clause.eval, List.any_eq_true]
  constructor
  · intro ha c hc
    obtain ⟨l, hl, he⟩ := ha c hc
    have hm : l.1 ∈ vars φ :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
    exact ⟨l, hl, by simpa only [Literal.eval, h l.1 hm] using he⟩
  · intro hb c hc
    obtain ⟨l, hl, he⟩ := hb c hc
    have hm : l.1 ∈ vars φ :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
    exact ⟨l, hl, by simpa only [Literal.eval, ← h l.1 hm] using he⟩

theorem weight_eq_of_agrees (φ : CNF) {a b : Assignment}
    (h : ∀ i ∈ vars φ, a i = b i) :
    ModelWeightChecking.weight φ a = ModelWeightChecking.weight φ b := by
  unfold ModelWeightChecking.weight
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [h j (List.mem_toFinset.mp hj)]

end PEqualNP.Outside.MinimumWeightModelGateCompiler
