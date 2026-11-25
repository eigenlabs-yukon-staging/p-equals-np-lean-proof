import PEqualNP.Outside.DavisPutnamElimination

namespace PEqualNP.Outside

open PEqualNP.ProofComplexity

private theorem concat_derivations (F : Set NatClause) {π τ : List NatClause}
    (hπ : IsDerivation F π) (hτ : IsDerivation F τ) : IsDerivation F (π ++ τ) := by
  induction hπ with
  | nil => exact hτ
  | ax _ ha ih => exact .ax ih ha
  | res _ ha hb hr ih => exact .res ih (List.mem_append_left _ ha) (List.mem_append_left _ hb) hr

private theorem transport_derivation (F G : Set NatClause) (allowed : NatClause → Prop)
    (axioms : ∀ C ∈ G, ∃ π : List NatClause, IsDerivation F π ∧ C ∈ π ∧ ∀ d ∈ π, allowed d)
    {ρ : List NatClause} (hρ : IsDerivation G ρ) (hw : ∀ d ∈ ρ, allowed d) :
    ∃ τ : List NatClause, IsDerivation F τ ∧ ρ ⊆ τ ∧ ∀ d ∈ τ, allowed d := by
  induction hρ with
  | nil => exact ⟨[],.nil,fun _ h => h,by simp⟩
  | @ax ρ C hD hC ih =>
      obtain ⟨τ,hτ,hsub,hAllow⟩ := ih (fun d h => hw d (List.mem_cons_of_mem _ h))
      obtain ⟨π,hπ,hπC,hπA⟩ := axioms C hC
      refine ⟨π ++ τ,concat_derivations F hπ hτ,?_,?_⟩
      · intro d h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_append_left _ hπC
        · exact List.mem_append_right _ (hsub h)
      · intro d h
        exact (List.mem_append.mp h).elim (hπA d) (hAllow d)
  | @res ρ A B C hD hA hB hC ih =>
      obtain ⟨τ,hτ,hsub,hAllow⟩ := ih (fun d h => hw d (List.mem_cons_of_mem _ h))
      refine ⟨C :: τ,.res hτ (hsub hA) (hsub hB) hC,?_,?_⟩
      · intro d h
        rcases List.mem_cons.mp h with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub hm)
      · intro d h
        rcases List.mem_cons.mp h with rfl | hm
        · exact hw _ List.mem_cons_self
        · exact hAllow d hm

private theorem elimination_axioms (x : ℕ) (F U : Set NatClause) (hF : F ⊆ U)
    (hNext : eliminateVariable x F ⊆ U) (C : NatClause) (hC : C ∈ eliminateVariable x F) :
    ∃ π : List NatClause, IsDerivation F π ∧ C ∈ π ∧ ∀ d ∈ π, d ∈ U := by
  rcases hC with ⟨hC,_,_⟩ | ⟨P,hP,N,hN,hp,hpn,hn,hnp,he⟩
  · exact ⟨[C],.ax .nil hC,List.mem_cons_self,by simpa using hF hC⟩
  · have hr : IsResolvent P N C := ⟨x,hp,hn,he⟩
    have hd : IsDerivation F [C,N,P] := by
      have hParents : IsDerivation F [N,P] := .ax (.ax .nil hP) hN
      exact .res hParents (by simp) (by simp) hr
    refine ⟨[C,N,P],hd,List.mem_cons_self,fun d hd => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact hNext (Or.inr ⟨P,hP,N,hN,hp,hpn,hn,hnp,he⟩)
    · exact hF hN
    · exact hF hP

def eliminationCovered (U : Set NatClause) : List ℕ → Set NatClause → Prop
  | [], F => F ⊆ U
  | x :: xs, F => F ⊆ U ∧ eliminationCovered U xs (eliminateVariable x F)

private theorem covered_start (U : Set NatClause) (xs : List ℕ) (F : Set NatClause)
    (h : eliminationCovered U xs F) : F ⊆ U := by
  cases xs with
  | nil => exact h
  | cons x xs => exact h.1

private theorem covered_of_prefix (U : Set NatClause) (xs : List ℕ) (F : Set NatClause)
    (h : ∀ i ≤ xs.length, (xs.take i).foldl (fun f x => eliminateVariable x f) F ⊆ U) :
    eliminationCovered U xs F := by
  induction xs generalizing F with
  | nil => exact h 0 (Nat.zero_le _) 
  | cons x xs ih =>
      refine ⟨h 0 (Nat.zero_le _),ih _ ?_⟩
      intro i hi
      exact h (i+1) (Nat.succ_le_succ hi)

private theorem proof_of_covered (U : Set NatClause) (order : List ℕ) (F : Set NatClause)
    (hSupp : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order)
    (hCovered : eliminationCovered U order F) (hUnsat : ¬ Satisfiable F) :
    ∃ π : List NatClause, IsRefutation F π ∧ ∀ c ∈ π, c ∈ U := by
  induction order generalizing F with
  | nil =>
      have h0 : ∅ ∈ F := by
        by_contra he
        apply hUnsat
        refine ⟨fun _ => false,fun c hc => ?_⟩
        have hz : c = ∅ := by
          ext l
          constructor
          · intro hl
            have hh := hSupp c hc l hl
            simp at hh
          · simp
        exact (he (hz ▸ hc)).elim
      exact ⟨[∅],⟨.ax .nil h0,List.mem_cons_self⟩,by simpa using (covered_start U [] F hCovered h0)⟩
  | cons x xs ih =>
      let G := eliminateVariable x F
      have hsub : F ⊆ U := hCovered.1
      have hCov : eliminationCovered U xs G := hCovered.2
      have hNeg : ¬ Satisfiable G := by
        apply mt _ hUnsat
        exact (DavisPutnamElimination x F).mp
      have hS : ∀ c ∈ G, ∀ l ∈ c, l.1 ∈ xs := by
        intro c hc l hl
        obtain ⟨hne,d,hd,hL⟩ := eliminate_support hc l hl
        exact (List.mem_cons.mp (hSupp d hd l hL)).resolve_left hne
      obtain ⟨π,⟨hπ,hEmpty⟩,hU⟩ := ih G hS hCov hNeg
      obtain ⟨τ,hτ,hInc,hτU⟩ := transport_derivation F G (fun c => c ∈ U)
        (elimination_axioms x F U hsub (covered_start U xs G hCov)) hπ hU
      exact ⟨τ,⟨hτ,hInc hEmpty⟩,hτU⟩

/-- A variable elimination order whose intermediate clauses lie in a
supplied universe certifies resolution coverage for every unsatisfiable input. -/
theorem EliminationOrderRefutation (F U : Set (PEqualNP.ProofComplexity.Clause ℕ)) (order : List ℕ) :
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    (∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order) →
    (∀ i ≤ order.length, (order.take i).foldl eliminate F ⊆ U) →
    ¬ Satisfiable F →
    ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ), IsRefutation F π ∧ ∀ c ∈ π, c ∈ U := by
  dsimp only
  intro hs hu hn
  exact proof_of_covered U order F hs (covered_of_prefix U order F hu) hn

end PEqualNP.Outside
