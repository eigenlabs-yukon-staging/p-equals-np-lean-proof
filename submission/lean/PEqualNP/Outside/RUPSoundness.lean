import PEqualNP.Outside.UnitPropagationCorrect

namespace PEqualNP.Outside

open PEqualNP.Search
open PEqualNP.ProofComplexity (ClauseSat Satisfies)

private theorem opposite (b c : Bool) (he : b = c) : b ≠ !c := by
  cases c <;> simp_all

private theorem neg_value (σ : Assignment) (l : Literal) (h : σ l.1 ≠ l.2) :
    σ (negLit l).1 = (negLit l).2 := by
  cases hl : l.2 <;> cases hs : σ l.1 <;> simp_all [negLit]

theorem unit_truth {Γ : Set FinClause} {A : Set Literal} {l : Literal}
    (h : UPForces Γ A l) (σ : Assignment) (hΓ : Satisfies σ Γ)
    (hA : ∀ l ∈ A, σ l.1 = l.2) : σ l.1 = l.2 := by
  induction h with
  | hyp h => exact hA _ h
  | @unit c l hc hl _ ih =>
      obtain ⟨m,hm,he⟩ := hΓ c hc
      by_cases hml : m = l
      · simpa only [hml] using he
      · exact (opposite _ _ he (ih m hm hml)).elim

theorem rup_truth {Γ : Set FinClause} {C : FinClause}
    (h : IsRUP Γ C) (σ : Assignment) (hΓ : Satisfies σ Γ) : ClauseSat σ C := by
  classical
  by_contra hn
  have hA : ∀ l ∈ negLit '' (↑C : Set Literal), σ l.1 = l.2 := by
    rintro l ⟨m,hm,rfl⟩
    exact neg_value σ m (fun he => hn ⟨m,hm,he⟩)
  obtain ⟨d,hd,hf⟩ := h
  obtain ⟨l,hl,he⟩ := hΓ d hd
  exact opposite _ _ he (unit_truth (hf l hl) σ hΓ hA)

private theorem run_truth {F : Set FinClause} {ρ : List FinClause}
    (hr : IsRUPRun F ρ) (σ : Assignment) (hF : Satisfies σ F) :
    ∀ c ∈ ρ, ClauseSat σ c := by
  induction hr with
  | nil => simp
  | @learn ρ C _ hstep ih =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · apply rup_truth hstep σ
        intro d hd
        rcases hd with hd | hd
        · exact hF d hd
        · exact ih d hd
      · exact ih c hc

theorem rup_run_refutes (φ ρ : CNF)
    (h : IsRUPRun (clauseSet φ) (ρ.map fun c => c.toFinset)) (he : [] ∈ ρ) :
    ¬Satisfiable φ := by
  rintro ⟨σ,hσ⟩
  have hφ : Satisfies σ (clauseSet φ) := by
    rintro c ⟨d,hd,rfl⟩
    obtain ⟨l,hl,he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hσ d hd)
    exact ⟨l,List.mem_toFinset.mpr hl,by simpa [Literal.eval] using he⟩
  have hnil : (∅ : FinClause) ∈ ρ.map (fun c => c.toFinset) :=
    List.mem_map.mpr ⟨[],he,rfl⟩
  obtain ⟨l,hl,_⟩ := run_truth h σ hφ ∅ hnil
  exact Finset.notMem_empty l hl

theorem clauseSet_append (φ ψ : CNF) :
    clauseSet (φ ++ ψ) = clauseSet φ ∪ {d | d ∈ ψ.map (fun c => c.toFinset)} := by
  ext c
  simp only [clauseSet,Set.mem_setOf_eq,Set.mem_union,List.mem_append,List.mem_map]
  constructor
  · rintro ⟨d,hd,he⟩
    exact hd.elim (fun h => Or.inl ⟨d,h,he⟩) (fun h => Or.inr ⟨d,h,he⟩)
  · rintro (⟨d,h,he⟩ | ⟨d,h,he⟩)
    · exact ⟨d,Or.inl h,he⟩
    · exact ⟨d,Or.inr h,he⟩

theorem rup_run_cons (φ ρ : CNF) (c : Clause) :
    IsRUPRun (clauseSet φ) ((c :: ρ).map (fun d => d.toFinset)) ↔
      IsRUP (clauseSet (φ ++ ρ)) c.toFinset ∧ IsRUPRun (clauseSet φ) (ρ.map (fun d => d.toFinset)) := by
  rw [List.map_cons,clauseSet_append]
  constructor
  · intro h
    cases h with
    | learn hr hh => exact ⟨hh,hr⟩
  · rintro ⟨hc,hr⟩
    exact .learn hr hc

end PEqualNP.Outside
