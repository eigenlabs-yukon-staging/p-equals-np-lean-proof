import PEqualNP.Outside.TwoSATShortRUP
import PEqualNP.Outside.ExactResolutionRefutationVerifier
import PEqualNP.Library.SearchHelpers.TwoSat

namespace PEqualNP.Outside

open PEqualNP.Search
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.ProofComplexity (IsDerivation IsRefutation IsResolvent)

private def endpoints (u v : Literal) : FinClause := {neg u,v}

private theorem pair_bound (a b : Literal) {C : FinClause} (h : C ⊆ ({a,b} : FinClause)) :
    C.card ≤ 2 := by
  apply (Finset.card_le_card h).trans
  exact (Finset.card_insert_le a ({b} : FinClause)).trans (by simp)

private theorem append_derivations (F : Set FinClause) {π τ : List FinClause}
    (hπ : IsDerivation F π) (hτ : IsDerivation F τ) : IsDerivation F (π ++ τ) := by
  induction hπ with
  | nil => exact hτ
  | ax _ hA ih => exact .ax ih hA
  | res _ hA hB hR ih =>
      exact .res ih (List.mem_append_left _ hA) (List.mem_append_left _ hB) hR

private theorem edge_clause {φ : CNF} {u v : Literal} (h : Edge φ u v) :
    ∃ C ∈ clauseSet φ, C ⊆ endpoints u v := by
  obtain ⟨c,hc,hl⟩ := h
  rcases (mem_forced_single c u v).mp hl with ⟨rfl,_⟩ | ⟨a,h,rfl⟩
  · refine ⟨([v] : Clause).toFinset,⟨[v],hc,rfl⟩,?_⟩
    intro l hl
    have he : l = v := List.mem_singleton.mp (List.mem_toFinset.mp hl)
    simp [endpoints,he]
  · rcases h with rfl | rfl
    · refine ⟨([a,v] : Clause).toFinset,⟨[a,v],hc,rfl⟩,?_⟩
      intro l hl
      have he := List.mem_toFinset.mp hl
      simpa [endpoints,PEqualNP.Library.SearchHelpers.TwoSat.neg_neg] using he
    · refine ⟨([v,a] : Clause).toFinset,⟨[v,a],hc,rfl⟩,?_⟩
      intro l hl
      have he := List.mem_toFinset.mp hl
      simpa [endpoints,PEqualNP.Library.SearchHelpers.TwoSat.neg_neg,or_comm] using he

private theorem pivot_resolution (m : Literal) (A B : FinClause) (hA : m ∈ A) (hB : neg m ∈ B) :
    IsResolvent A B (A.erase m ∪ B.erase (neg m)) ∨
      IsResolvent B A (A.erase m ∪ B.erase (neg m)) := by
  obtain ⟨v,b⟩ := m
  cases b
  · exact Or.inr ⟨v,hB,hA,Finset.union_comm _ _⟩
  · exact Or.inl ⟨v,hA,hB,rfl⟩

private theorem join_endpoints (u m v : Literal) (A B : FinClause)
    (hA : A ⊆ endpoints u m) (hB : B ⊆ endpoints m v) :
    ∃ C : FinClause, C ⊆ endpoints u v ∧ (C = A ∨ C = B ∨ IsResolvent A B C ∨ IsResolvent B A C) := by
  by_cases h : m ∈ A
  · by_cases hn : neg m ∈ B
    · refine ⟨A.erase m ∪ B.erase (neg m),?_,Or.inr (Or.inr (pivot_resolution m A B h hn))⟩
      intro l hl
      rcases Finset.mem_union.mp hl with hl | hl
      · obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hl
        have hh := hA hm
        simp only [endpoints,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
        exact Or.inl (hh.resolve_right hne)
      · obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hl
        have hh := hB hm
        simp only [endpoints,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
        exact Or.inr (hh.resolve_left hne)
    · refine ⟨B,?_,Or.inr (Or.inl rfl)⟩
      intro l hl
      have he := hB hl
      simp only [endpoints,Finset.mem_insert,Finset.mem_singleton] at he ⊢
      exact Or.inr (he.resolve_left (fun h => hn (h ▸ hl)))
  · refine ⟨A,?_,Or.inl rfl⟩
    intro l hl
    have he := hA hl
    simp only [endpoints,Finset.mem_insert,Finset.mem_singleton] at he ⊢
    exact Or.inl (he.resolve_right (fun e => h (e ▸ hl)))

private theorem path_derivation {φ : CNF} {u v : Literal} (h : Reach φ u v) (hne : v ≠ u) :
    ∃ (π : List FinClause) (C : FinClause), IsDerivation (clauseSet φ) π ∧
      (∀ d ∈ π, d.card ≤ 2) ∧ C ∈ π ∧ C ⊆ endpoints u v := by
  induction h with
  | refl => exact (hne rfl).elim
  | @tail m v hm hstep ih =>
      obtain ⟨B,hB,hBV⟩ := edge_clause hstep
      have hb : B.card ≤ 2 := pair_bound _ _ hBV
      by_cases hed : m = u
      · subst m
        exact ⟨[B],B,.ax .nil hB,by simpa using hb,by simp,hBV⟩
      · obtain ⟨π,A,hπ,hWidth,hA,hSub⟩ := ih hed
        let chain := B :: π
        have hChain : IsDerivation (clauseSet φ) chain := .ax hπ hB
        have hWidth' (C : FinClause) (hc : C ∈ chain) : C.card ≤ 2 := by
          rcases List.mem_cons.mp hc with rfl | h
          · exact hb
          · exact hWidth C h
        have ha' : A ∈ chain := List.mem_cons_of_mem _ hA
        have hb' : B ∈ chain := List.mem_cons_self
        obtain ⟨C,hCv,hCase⟩ := join_endpoints u m v A B hSub hBV
        rcases hCase with hEq | hEq | hR | hR
        · subst C
          exact ⟨chain,A,hChain,hWidth',ha',hCv⟩
        · subst C
          exact ⟨chain,B,hChain,hWidth',hb',hCv⟩
        · exact ⟨C :: chain,C,.res hChain ha' hb' hR,fun d hd =>
            (List.mem_cons.mp hd).elim (fun eq => eq.symm ▸ pair_bound _ _ hCv) (hWidth' d),List.mem_cons_self,hCv⟩
        · exact ⟨C :: chain,C,.res hChain hb' ha' hR,fun d hd =>
            (List.mem_cons.mp hd).elim (fun eq => eq.symm ▸ pair_bound _ _ hCv) (hWidth' d),List.mem_cons_self,hCv⟩

private theorem empty_or_unit (d : FinClause) (u : Literal) (h : d ⊆ ({u} : FinClause)) :
    d = ∅ ∨ d = {u} := by
  rcases d.eq_empty_or_nonempty with h0 | ⟨l,hl⟩
  · exact Or.inl h0
  · right
    apply Finset.Subset.antisymm h
    have he : l = u := Finset.mem_singleton.mp (h hl)
    intro m hm
    have hm' := Finset.mem_singleton.mp hm
    rwa [hm',← he]

private theorem neg_different (u : Literal) : neg u ≠ u := by
  obtain ⟨i,b⟩ := u
  cases b <;> simp [neg]

private theorem refutation_of_conflict {φ : CNF} {u : Literal}
    (h1 : Reach φ u (neg u)) (h2 : Reach φ (neg u) u) :
    ∃ π : List FinClause, IsRefutation (clauseSet φ) π ∧ ∀ d ∈ π, d.card ≤ 2 := by
  obtain ⟨π,A,hπ,hWidth,hA,ha⟩ := path_derivation h1 (neg_different u)
  obtain ⟨τ,B,hτ,hwidth,hB,hb⟩ := path_derivation h2 (Ne.symm (neg_different u))
  have hU : A ⊆ ({neg u} : FinClause) := by simpa [endpoints] using ha
  have hV : B ⊆ ({u} : FinClause) := by
    simpa [endpoints,PEqualNP.Library.SearchHelpers.TwoSat.neg_neg] using hb
  rcases empty_or_unit A (neg u) hU with rfl | hAEq
  · exact ⟨π,⟨hπ,hA⟩,hWidth⟩
  rcases empty_or_unit B u hV with rfl | hBEq
  · exact ⟨τ,⟨hτ,hB⟩,hwidth⟩
  have hAppend := append_derivations (clauseSet φ) hπ hτ
  have ha' : A ∈ π ++ τ := List.mem_append_left _ hA
  have hb' : B ∈ π ++ τ := List.mem_append_right _ hB
  have hNew : IsDerivation (clauseSet φ) (∅ :: (π ++ τ)) := by
    have hp : u ∈ B := by simp [hBEq]
    have hn : neg u ∈ A := by simp [hAEq]
    have hR := pivot_resolution u B A hp hn
    have he : B.erase u ∪ A.erase (neg u) = ∅ := by simp [hBEq,hAEq]
    rw [he] at hR
    rcases hR with hR | hR
    · exact .res hAppend hb' ha' hR
    · exact .res hAppend ha' hb' hR
  refine ⟨∅ :: (π ++ τ),⟨hNew,by simp⟩,fun C h => ?_⟩
  rcases List.mem_cons.mp h with rfl | hc
  · simp
  · rcases List.mem_append.mp hc with hc | hc
    · exact hWidth C hc
    · exact hwidth C hc

/-- Width-two canonical formulas are unsatisfiable exactly when they admit
a resolution refutation that never uses a clause wider than two. -/
theorem TwoSATWidthTwoRefutation (φ : CNF) (hW : IsKCNF 2 φ) :
    ¬Satisfiable φ ↔ ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
      IsRefutation {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
      ∀ d ∈ π, Finset.card d ≤ 2 := by
  constructor
  · intro h
    by_cases he : [] ∈ φ
    · exact ⟨[∅],⟨.ax .nil ⟨[],he,List.toFinset_nil⟩,List.mem_cons_self⟩,by simp⟩
    · obtain ⟨c,hc,l,hl,h1,h2⟩ := twoSat_conflict φ hW he h
      exact refutation_of_conflict h1 h2
  · rintro ⟨π,hπ,_⟩
    let ρ := π.map Finset.toList
    have he : ρ.map List.toFinset = π := by simp [ρ,List.map_map,Function.comp_def,Finset.toList_toFinset]
    apply ExactResolutionRefutationVerifier.2 φ ρ
    rw [he]
    exact hπ

end PEqualNP.Outside
