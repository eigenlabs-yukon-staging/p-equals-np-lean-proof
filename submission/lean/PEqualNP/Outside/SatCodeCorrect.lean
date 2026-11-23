import PEqualNP.Outside.SatCodeSemantics

namespace PEqualNP.Outside.SatCodeCorrect

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodeDecoder PEqualNP.Outside.SatCodeSemantics

theorem coded_run (σ : Assignment) (ts : List Token) (s out : List ℕ) :
    let ns := newVars s ts
    step^[ts.length] (pack (encTokens ts) (s.flatMap vcode) (ns.map σ) (out.flatMap vcode)) =
      pack [] ((s ++ ns).flatMap vcode) [] ((out ++ ns.filter σ).flatMap vcode) := by
  induction ts generalizing s out with
  | nil => simp [newVars, encTokens]
  | cons t ts ih =>
    cases t with
    | none =>
      simp only [newVars, List.length_cons, encTokens, List.flatMap_cons, encToken,
        Function.iterate_succ_apply, step_skip]
      exact ih s out
    | some l =>
      by_cases hm : l.1 ∈ s
      · simp only [newVars, hm, ite_true, List.length_cons, encTokens, List.flatMap_cons,
          encToken, Function.iterate_succ_apply, step_known l _ s _ _ hm]
        exact ih s out
      · simp only [newVars, hm, ite_false, List.length_cons, encTokens, List.flatMap_cons,
          encToken, List.map_cons, Function.iterate_succ_apply, step_fresh l _ s _ _ _ hm]
        cases hb : σ l.1
        · simpa [encTokens, hb, List.append_assoc] using ih (s ++ [l.1]) out
        · simpa [encTokens, hb, List.append_assoc, List.flatMap_append] using ih (s ++ [l.1]) (out ++ [l.1])

theorem token_len (t : Token) : 1 ≤ (encToken t).length := by
  cases t <;> simp [encToken, encodeLiteral]

theorem tokens_len (ts : List Token) : ts.length ≤ (encTokens ts).length := by
  induction ts with
  | nil => simp [encTokens]
  | cons t ts ih =>
    have ht := token_len t
    simp only [encTokens, List.length_cons, List.flatMap_cons, List.length_append] at ih ⊢
    omega

theorem newVars_enc_length (ts : List Token) (s : List ℕ) :
    ((newVars s ts).flatMap vcode).length ≤ (encTokens ts).length := by
  induction ts generalizing s with
  | nil => simp [newVars, encTokens]
  | cons t ts ih =>
    cases t with
    | none =>
      have h := ih s
      simp only [newVars, encTokens, List.flatMap_cons, encToken, List.length_append] at h ⊢
      omega
    | some l =>
      by_cases hm : l.1 ∈ s
      · have h := ih s
        simp only [newVars, hm, ite_true, encTokens, List.flatMap_cons, encToken,
          List.length_append] at h ⊢
        omega
      · have h := ih (s ++ [l.1])
        simp [newVars, hm, encTokens, encToken, encodeLiteral_eq, List.flatMap_cons] at h ⊢
        omega

theorem decode_on_assignment (φ : CNF) (σ : Assignment) :
    let varList := newVars [] (tokens φ)
    decode (encodeCNF φ, varList.map σ) = (varList.filter σ).flatMap vcode := by
  let ts := tokens φ
  let vars := newVars [] ts
  have henc : encTokens ts = encodeCNF φ := encode_tokens φ
  have hlen : ts.length ≤ (encodeCNF φ).length := henc ▸ tokens_len ts
  have hrun := coded_run σ ts [] []
  simp only [List.nil_append, List.flatMap_nil, henc] at hrun
  change output (step^[(encodeCNF φ).length]
    (pack (encodeCNF φ) [] (vars.map σ) [])) = _
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, hrun,
    Function.iterate_fixed (step_empty _ _ _)]
  simp [output, pack, unpairB_pairB, ts]

theorem code_of_sat (φ : CNF) (h : Satisfiable φ) :
    ∃ code : List Bool,
      code.length ≤ (support φ).length ∧
      (decode (encodeCNF φ, code)).length ≤ (encodeCNF φ).length ∧
      SV (encodeCNF φ, decode (encodeCNF φ, code)) = true := by
  obtain ⟨σ, hσ⟩ := h
  let vars := newVars [] (tokens φ)
  refine ⟨vars.map σ, by simpa only [vars, List.length_map] using vars_count_le φ, ?_, ?_⟩
  · rw [decode_on_assignment]
    exact (length_filter_flatMap σ vcode vars).trans
      ((encode_tokens φ) ▸ newVars_enc_length (tokens φ) [])
  · apply (SV_iff _ _).mpr
    refine ⟨φ, rfl, ?_⟩
    rw [decode_on_assignment]
    simp only [CNF.eval, List.all_eq_true, Clause.eval, List.any_eq_true] at hσ ⊢
    intro c hc
    obtain ⟨l, hl, hval⟩ := hσ c hc
    refine ⟨l, hl, ?_⟩
    have hmem : l.1 ∈ vars :=
      (mem_newVars l.1 [] (tokens φ)).mpr ⟨by simp, by
        rw [ids_tokens]
        exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩⟩
    have hagree : asg ((vars.filter σ).flatMap vcode) l.1 = σ l.1 := by
      rw [Bool.eq_iff_iff]
      exact (asg_codes _ _).trans (by simp [List.mem_filter, hmem])
    change Literal.eval (asg ((vars.filter σ).flatMap vcode)) l = true
    simpa [Literal.eval, hagree] using hval

end PEqualNP.Outside.SatCodeCorrect
