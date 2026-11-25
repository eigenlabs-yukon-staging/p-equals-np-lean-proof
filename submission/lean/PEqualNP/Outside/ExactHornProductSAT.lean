import PEqualNP.Outside.ExactClausePartitionProductSAT
import PEqualNP.Outside.MeasuredHornSAT
import PEqualNP.Outside.MeasuredHornGuard
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Search

/-- Product-bounded exceptions to Horn syntax can be handled by measured branching
into unit-augmented Horn formulas. -/
theorem ExactHornProductSAT (q : Polynomial ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ((φ.filter (fun c => 1 < (c.filter fun l => l.2).length)).map List.length).prod ≤ q.eval x.length ∧
      Satisfiable φ} ∈ P := by
  obtain ⟨test,haccept,hc⟩ := MeasuredHornGuard
  obtain ⟨B,hB,hBSat⟩ := MeasuredHornSAT
  have hspec (c : Clause) : test (encodeClause c) = true ↔ (c.filter fun l => l.2).length ≤ 1 := by
    have e : encodeCNF [c] = encodeClause c := by simp [encodeCNF]
    rw [← haccept,← e]
    change (∃ φ : CNF, encodeCNF φ = encodeCNF [c] ∧
      ∀ d ∈ φ, (d.filter fun l => l.2).length ≤ 1) ↔ _
    constructor
    · rintro ⟨φ,hφ,ha⟩
      have he := PEqualNP.Library.SearchHelpers.encodeCNF_injective hφ
      subst φ
      exact ha c List.mem_cons_self
    · intro h
      exact ⟨[c],rfl,by simpa using h⟩
  have hunit (c : Clause) (hl : c.length ≤ 1) : test (encodeClause c) = true :=
    (hspec c).mpr ((List.length_filter_le _ _).trans hl)
  have hbase (φ : CNF) (h : ∀ c ∈ φ, test (encodeClause c) = true) :
      encodeCNF φ ∈ B ↔ Satisfiable φ := hBSat φ (fun c hc => (hspec c).mp (h c hc))
  have h := ExactClausePartitionProductSAT test hc B hB hunit hbase q
  have hflag : (fun c : Clause => !test (encodeClause c)) =
      (fun c => decide (1 < (c.filter fun l => l.2).length)) := by
    funext c
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_iff]
    exact ⟨fun hn => by
      by_contra hh
      exact (Bool.noConfusion (hn.symm.trans ((hspec c).mpr (by omega)))),
      fun hl => Bool.eq_false_iff.mpr (fun he => Nat.not_lt_of_ge ((hspec c).mp he) hl)⟩
  rwa [hflag] at h

end PEqualNP.Outside
