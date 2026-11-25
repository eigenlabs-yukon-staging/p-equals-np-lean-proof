import PEqualNP.Outside.DavisPutnamElimination
import PEqualNP.Outside.UnitPropagationCorrect
import PEqualNP.Library.SearchHelpers.SatVerifier

namespace PEqualNP.Outside

open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open PEqualNP.ProofComplexity (Satisfies)

theorem cnf_satisfies_iff (a : Assignment) (φ : CNF) :
    CNF.eval a φ = true ↔ Satisfies a (clauseSet φ) := by
  simp only [CNF.eval,List.all_eq_true,Clause.eval,List.any_eq_true,Literal.eval,beq_iff_eq]
  constructor
  · rintro h C ⟨c,hc,rfl⟩
    obtain ⟨l,hl,ha⟩ := h c hc
    exact ⟨l,List.mem_toFinset.mpr hl,ha⟩
  · intro h c hc
    obtain ⟨l,hl,ha⟩ := h c.toFinset ⟨c,hc,rfl⟩
    exact ⟨l,List.mem_toFinset.mp hl,ha⟩

theorem sv_satisfies_iff (φ : CNF) (w : List Bool) :
    SV (encodeCNF φ,w) = true ↔ Satisfies (asg w) (clauseSet φ) := by
  have hw := (wfB_iff (encodeCNF φ)).mpr ⟨φ,rfl⟩
  simp only [SV,hw,Bool.true_and,evalB_enc,cnf_satisfies_iff]

private theorem update_false (x : ℕ) (vs : List ℕ) (hx : x ∉ vs) :
    Function.update (asg (vs.flatMap vcode)) x false = asg (vs.flatMap vcode) := by
  funext y
  by_cases hy : y = x
  · subst y
    have hfalse := Bool.eq_false_iff.mpr (fun h => hx ((asg_codes _ _).mp h))
    simp [hfalse]
  · simp [Function.update_of_ne hy]

private theorem update_true (x : ℕ) (vs : List ℕ) :
    Function.update (asg (vs.flatMap vcode)) x true = asg ((x::vs).flatMap vcode) := by
  funext y
  apply Bool.eq_iff_iff.mpr
  by_cases hy : y = x
  · subst y
    rw [Function.update_self,asg_codes]
    simp
  · rw [Function.update_of_ne hy,asg_codes,asg_codes]
    simp [hy]

theorem lift_codes (φ : CNF) (x : ℕ) (vs : List ℕ) (hx : x ∉ vs)
    (h : Satisfies (asg (vs.flatMap vcode)) (eliminateVariable x (clauseSet φ))) :
    Satisfies (asg ((if SV (encodeCNF φ,vs.flatMap vcode) then vs else x::vs).flatMap vcode))
      (clauseSet φ) := by
  by_cases hs : SV (encodeCNF φ,vs.flatMap vcode) = true
  · simp only [hs,ite_true]
    exact (sv_satisfies_iff _ _).mp hs
  · obtain ⟨b,hb⟩ := lift_eliminate_assignment x (clauseSet φ) _ h
    have hf : SV (encodeCNF φ,vs.flatMap vcode) = false := Bool.eq_false_iff.mpr hs
    cases b with
    | false =>
      rw [update_false _ _ hx] at hb
      exact (hs ((sv_satisfies_iff _ _).mpr hb)).elim
    | true =>
      simpa only [hf,Bool.false_eq_true,ite_false,← update_true] using hb

end PEqualNP.Outside
