import PEqualNP.Outside.OneHotTableau

namespace PEqualNP.Outside.OneHot
open PEqualNP.Library.Universal PEqualNP.Search PEqualNP.Library.SearchHelpers.Tab

theorem width_append {k : ℕ} {F G : CNF} :
    IsKCNF k (F ++ G) ↔ IsKCNF k F ∧ IsKCNF k G := by
  simp only [IsKCNF, List.mem_append, or_imp, forall_and]

theorem width_map {α : Type} {k : ℕ} {xs : List α} {f : α → Clause} :
    IsKCNF k (xs.map f) ↔ ∀ x ∈ xs, (f x).length ≤ k := by
  simp only [IsKCNF,List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h x hx
    exact h (f x) x hx rfl
  · rintro h _ x hx rfl
    exact h x hx

theorem width_flatMap {α : Type} {k : ℕ} {xs : List α} {f : α → CNF} :
    IsKCNF k (xs.flatMap f) ↔ ∀ x ∈ xs, IsKCNF k (f x) := by
  constructor
  · intro h x hx cl hc
    exact h cl (List.mem_flatMap.mpr ⟨x,hx,hc⟩)
  · intro h cl hc
    obtain ⟨x,hx,hc⟩ := List.mem_flatMap.mp hc
    exact h x hx cl hc

theorem read_width (K B t : ℕ) (o : Option ℕ) (r : List ℕ × ℕ) (hr : r ∈ reads K B t o) :
    r.1.length ≤ 1 := by
  cases o with
  | none =>
    have e : r = ([],0) := by simpa [reads] using hr
    simp [e]
  | some k =>
    simp only [reads] at hr
    split at hr
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
      simp
    · have e : r = ([],0) := by simpa using hr
      simp [e]

theorem step_width (K H B t : ℕ) (P : List Instr) :
    IsKCNF 4 (stepClauses K H B P t) := by
  simp only [stepClauses, width_flatMap, width_append]
  intro q _
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp [pcClauses,width_map,imp]
  · simp only [stateClauses,width_flatMap,width_map]
    intro v _ r hr
    have hr' := read_width K B t _ r hr
    simp only [imp,List.length_append,List.length_map,List.length_cons,List.length_nil]
    omega
  · intro k _
    cases stackOp (instrAt P q) k <;>
      simp only [cellClauses,width_append,width_flatMap,width_map] <;>
      simp [IsKCNF,imp]

theorem init_width (c : Code) (zs : List ℕ) (m H : ℕ) :
    IsKCNF 4 (initClauses c zs m H) := by
  simp only [initClauses,width_append,width_flatMap,width_map]
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp [IsKCNF,imp]
  · intro k _
    split <;> simp [IsKCNF,width_map,imp]
  · split
    · simp only [width_append,width_map]; simp [IsKCNF,imp]
    · simp [IsKCNF]

theorem final_width (c : Code) (B T : ℕ) :
    IsKCNF 4 (finalClauses c B T) := by
  simp only [finalClauses,width_append,width_map]
  constructor
  · simp
  · split
    · simp only [width_append,width_flatMap,width_map]
      refine ⟨⟨?_,?_⟩,?_⟩
      · simp [IsKCNF]
      · intro x _
        split <;> simp [IsKCNF]
      · simp
    · simp [IsKCNF]

theorem formula_width (c : Code) (zs : List ℕ) (m T : ℕ) :
    IsKCNF 4 (formula c zs m T) := by
  simp only [formula,tableau,strengthening,width_append,width_flatMap]
  refine ⟨⟨⟨init_width c zs m _,fun t _ => step_width c.nstk _ (bound c) t c.prog⟩,final_width c (bound c) T⟩,?_⟩
  intro ⟨n,f⟩ _
  simp [pairs,width_flatMap,width_map]

end PEqualNP.Outside.OneHot
