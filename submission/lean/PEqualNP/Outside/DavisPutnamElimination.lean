import PEqualNP.ProofComplexity.Helpers.Resolution

namespace PEqualNP.Outside

open PEqualNP.ProofComplexity

abbrev NatClause := Clause ℕ

def eliminateVariable (x : ℕ) (F : Set NatClause) : Set NatClause :=
  {C | (C ∈ F ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
    ∃ P ∈ F, ∃ N ∈ F, (x,true) ∈ P ∧ (x,false) ∉ P ∧
      (x,false) ∈ N ∧ (x,true) ∉ N ∧
      C = P.erase (x,true) ∪ N.erase (x,false)}

private theorem no_var {x : ℕ} {C : NatClause} (hp : (x,true) ∉ C) (hn : (x,false) ∉ C) :
    ∀ l ∈ C, l.1 ≠ x := by
  rintro ⟨v,b⟩ hl h
  change v = x at h
  subst v
  cases b
  · exact hn hl
  · exact hp hl

private theorem erase_opposite_no_var {x : ℕ} {b : Bool} {C : NatClause}
    (h : (x,!b) ∉ C) : ∀ l ∈ C.erase (x,b), l.1 ≠ x := by
  cases b
  · exact no_var (fun hp => h (Finset.mem_erase.mp hp).2) (by simp)
  · exact no_var (by simp) (fun hn => h (Finset.mem_erase.mp hn).2)

private theorem updated_clause {a : ℕ → Bool} {C : NatClause} {x : ℕ} {b : Bool}
    (h : ∀ l ∈ C, l.1 ≠ x) (ha : ClauseSat a C) : ClauseSat (Function.update a x b) C := by
  obtain ⟨l,hl,he⟩ := ha
  exact ⟨l,hl,(Function.update_of_ne (h l hl) b a).trans he⟩

private theorem extend_clause {a : ℕ → Bool} {C D : NatClause}
    (hsub : C ⊆ D) (ha : ClauseSat a C) : ClauseSat a D := by
  obtain ⟨l,hl,he⟩ := ha
  exact ⟨l,hsub hl,he⟩

private theorem updated_pivot (a : ℕ → Bool) {C : NatClause} (x : ℕ) (b : Bool)
    (h : (x,b) ∈ C) : ClauseSat (Function.update a x b) C := ⟨(x,b),h,by simp⟩

theorem satisfies_eliminate (x : ℕ) (F : Set NatClause) (a : ℕ → Bool)
    (h : Satisfies a F) : Satisfies a (eliminateVariable x F) := by
  rintro C (⟨hF,_,_⟩ | ⟨P,hP,N,hN,hp,_,hn,_,he⟩)
  · exact h C hF
  · exact PEqualNP.ProofComplexity.Helpers.resolvent_sound a ⟨x,hp,hn,he⟩ (h P hP) (h N hN)

theorem lift_eliminate_assignment (x : ℕ) (F : Set NatClause) (a : ℕ → Bool)
    (ha : Satisfies a (eliminateVariable x F)) :
    ∃ b : Bool, Satisfies (Function.update a x b) F := by
  classical
  let force := ∃ P ∈ F, (x,true) ∈ P ∧ (x,false) ∉ P ∧ ¬ ClauseSat a (P.erase (x,true))
  by_cases hforce : force
  · refine ⟨true,fun C hc => ?_⟩
    by_cases hp : (x,true) ∈ C
    · exact updated_pivot a x true hp
    · by_cases hn : (x,false) ∈ C
      · have hs : ClauseSat a (C.erase (x,false)) := by
          obtain ⟨P,hP,hp',hn',hbad⟩ := hforce
          have hC : P.erase (x,true) ∪ C.erase (x,false) ∈ eliminateVariable x F :=
            Or.inr ⟨P,hP,C,hc,hp',hn',hn,hp,rfl⟩
          obtain ⟨l,hl,hv⟩ := ha _ hC
          rcases Finset.mem_union.mp hl with h | h
          · exact (hbad ⟨l,h,hv⟩).elim
          · exact ⟨l,h,hv⟩
        have he : (x,!false) ∉ C := hp
        exact extend_clause (Finset.erase_subset _ _) (updated_clause (erase_opposite_no_var he) hs)
      · exact updated_clause (no_var hp hn) (ha C (Or.inl ⟨hc,hp,hn⟩))
  · refine ⟨false,fun C hc => ?_⟩
    by_cases hn : (x,false) ∈ C
    · exact updated_pivot a x false hn
    · by_cases hp : (x,true) ∈ C
      · have hs : ClauseSat a (C.erase (x,true)) := by
          by_contra hbad
          exact hforce ⟨C,hc,hp,hn,hbad⟩
        have he : (x,!true) ∉ C := hn
        exact extend_clause (Finset.erase_subset _ _) (updated_clause (erase_opposite_no_var he) hs)
      · exact updated_clause (no_var hp hn) (ha C (Or.inl ⟨hc,hp,hn⟩))

/-- Davis–Putnam elimination preserves satisfiability by retaining clauses
without the variable and resolving the opposite one-sided clauses. -/
theorem DavisPutnamElimination (x : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause ℕ)) :
    Satisfiable
      {C | (C ∈ F ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ F, ∃ N ∈ F, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ↔ Satisfiable F := by
  change Satisfiable (eliminateVariable x F) ↔ Satisfiable F
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := lift_eliminate_assignment x F a ha
    exact ⟨Function.update a x b,hb⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,satisfies_eliminate x F a ha⟩

theorem eliminate_support {x : ℕ} {F : Set NatClause} {C : NatClause} (hc : C ∈ eliminateVariable x F) :
    ∀ l ∈ C, l.1 ≠ x ∧ ∃ D ∈ F, l ∈ D := by
  intro l hl
  rcases hc with ⟨hc,hp,hn⟩ | ⟨P,hP,N,hN,hp,hpn,hn,hnp,rfl⟩
  · exact ⟨no_var hp hn l hl,C,hc,hl⟩
  · rcases Finset.mem_union.mp hl with hp' | hn'
    · have hz : (x,!true) ∉ P := hpn
      exact ⟨erase_opposite_no_var hz l hp',P,hP,(Finset.mem_erase.mp hp').2⟩
    · have hz : (x,!false) ∉ N := hnp
      exact ⟨erase_opposite_no_var hz l hn',N,hN,(Finset.mem_erase.mp hn').2⟩

end PEqualNP.Outside
