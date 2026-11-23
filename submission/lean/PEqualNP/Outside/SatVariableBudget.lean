import PEqualNP.Outside.SatCodeCorrect
import PEqualNP.Library.Universal.LazyDefs
import PEqualNP.Library.L055

namespace PEqualNP.Outside.SatVariableBudget

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV
open SatCodeDecoder SatCodeSemantics SatCodeCorrect SatCodePrimitives

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

theorem step_fresh_empty (l : Literal) (r : Word) (s : List ℕ) (h : l.1 ∉ s) :
    step (pack (encodeLiteral l ++ r) (s.flatMap vcode) [] []) =
      pack r ((s ++ [l.1]).flatMap vcode) [] [] := by
  have hm : memB (vcode l.1) (s.flatMap vcode) = false := by
    cases hbit : memB (vcode l.1) (s.flatMap vcode)
    · rfl
    · exact False.elim (h ((asg_codes s l.1).mp hbit))
  simp only [step, pack, item, remaining, seen, bits, output, unpairB_pairB, headI_lit, dropI_lit]
  simp [encodeLiteral_eq, hm, bflag, sel, vcode_ne_nil, List.flatMap_append]

theorem empty_code_run (ts : List Token) (s : List ℕ) :
    step^[ts.length] (pack (encTokens ts) (s.flatMap vcode) [] []) =
      pack [] ((s ++ newVars s ts).flatMap vcode) [] [] := by
  induction ts generalizing s with
  | nil => simp [encTokens, newVars]
  | cons t ts ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    cases t with
    | none =>
      simpa only [newVars, encTokens, List.flatMap_cons, encToken, step_skip] using ih s
    | some l =>
      by_cases hm : l.1 ∈ s
      · simpa only [newVars, hm, ite_true, encTokens, List.flatMap_cons, encToken,
          step_known l _ s _ _ hm] using ih s
      · simpa only [newVars, hm, ite_false, encTokens, List.flatMap_cons, encToken,
          step_fresh_empty l _ s hm, List.append_assoc, List.singleton_append] using ih (s ++ [l.1])

def seenNames (x : Word) : Word := seen (finalState (x, []))

theorem seenNames_cpt : CPT seenNames := by
  have h := cpt_comp (cpt_pair cpt_id (cpt_const [])) seen_cpt
  exact h

theorem seenNames_enc (φ : CNF) :
    seenNames (encodeCNF φ) = (newVars [] (tokens φ)).flatMap vcode := by
  let ts := tokens φ
  have henc : encTokens ts = encodeCNF φ := encode_tokens φ
  have hlen : ts.length ≤ (encodeCNF φ).length := henc ▸ tokens_len ts
  have hrun := empty_code_run ts []
  simp only [List.nil_append, List.flatMap_nil, henc] at hrun
  change seen (step^[(encodeCNF φ).length] (pack (encodeCNF φ) [] [] [])) = _
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, hrun,
    Function.iterate_fixed (step_empty _ _ _)]
  simp [seen, pack, unpairB_pairB, ts]


theorem half_cpt : CPT half :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

def spendStep (z : Word) : Word :=
  let r := (unpairB z).1
  let budget := (unpairB z).2
  sel r z (pairB (dropI r) (half budget))

theorem spendStep_length (z : Word) : (spendStep z).length ≤ z.length + 1 := by
  have h := unpairB_length z
  have hr := dropI_length (unpairB z).1
  simp only [spendStep, sel]
  split
  · omega
  · rw [pairB_length, half_eq, un_length]
    omega

theorem spendStep_cpt : CPT spendStep :=
  cptl (cpt_sel cpt_unpairB1 cpt_id
    (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropI) (cpt_comp cpt_unpairB2 half_cpt))) (fun _ => rfl)

theorem spendStep_empty (n : ℕ) : spendStep (pairB [] (un n)) = pairB [] (un n) := by
  simp [spendStep, sel, unpairB_pairB]

theorem spendStep_code (v : ℕ) (r : Word) (n : ℕ) :
    spendStep (pairB (vcode v ++ r) (un n)) = pairB r (un (n / 2)) := by
  simp [spendStep, sel, unpairB_pairB, vcode_ne_nil, dropI_vcode, half_eq, un_length]

theorem spend_code_run (vs : List ℕ) (n : ℕ) :
    spendStep^[vs.length] (pairB (vs.flatMap vcode) (un n)) =
      pairB [] (un (n / 2 ^ vs.length)) := by
  induction vs generalizing n with
  | nil => simp
  | cons v vs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons, spendStep_code, ih,
      Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

def spend (p : Polynomial ℕ) (x : Word) : Word :=
  (unpairB (spendStep^[(seenNames x).length] (pairB (seenNames x) (un (p.eval x.length))))).2

theorem spend_cpt (p : Polynomial ℕ) : CPT (spend p) := by
  have hseed := cpt_pairB2 seenNames_cpt (L055 p)
  have h := cpt_unpairB2_1 (cpt_iterGrow spendStep_cpt 1 spendStep_length seenNames_cpt hseed)
  exact cptl h (fun _ => rfl)

theorem spend_enc (p : Polynomial ℕ) (φ : CNF) :
    spend p (encodeCNF φ) = un (p.eval (encodeCNF φ).length /
      2 ^ (φ.flatten.map Prod.fst).toFinset.card) := by
  let vs := newVars [] (tokens φ)
  have hlen : vs.length ≤ (vs.flatMap vcode).length := length_le_flatMap_vcode vs
  have hcount := count_newVars φ
  simp only [spend, seenNames_enc]
  change (unpairB (spendStep^[(vs.flatMap vcode).length]
    (pairB (vs.flatMap vcode) (un (p.eval (encodeCNF φ).length))))).2 = _
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, spend_code_run,
    Function.iterate_fixed (spendStep_empty _), unpairB_pairB]
  exact congrArg (fun k => un (p.eval (encodeCNF φ).length / 2 ^ k)) hcount

end PEqualNP.Outside.SatVariableBudget
