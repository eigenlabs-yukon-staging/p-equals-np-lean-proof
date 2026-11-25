import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.Search

def flipLiteral (flip : Assignment) (l : Literal) : Literal := (l.1, xor l.2 (flip l.1))

def flipFormula (flip : Assignment) (φ : CNF) : CNF :=
  φ.map (fun c => c.map (flipLiteral flip))

def hornPairClauses : Clause → CNF
  | [] => []
  | l :: ls => (ls.map (fun m => [l,m])) ++ hornPairClauses ls

def hornRenamingConstraints (φ : CNF) : CNF := φ.flatMap hornPairClauses

private theorem eval_lit_flip (flip σ : Assignment) (l : Literal) :
    Literal.eval (fun i => xor (σ i) (flip i)) (flipLiteral flip l) = Literal.eval σ l := by
  simp only [Literal.eval,flipLiteral]
  cases σ l.1 <;> cases flip l.1 <;> cases l.2 <;> rfl

theorem flip_preserves_sat (flip : Assignment) (φ : CNF) :
    Satisfiable (flipFormula flip φ) ↔ Satisfiable φ := by
  have h (σ : Assignment) :
      CNF.eval (fun i => xor (σ i) (flip i)) (flipFormula flip φ) = CNF.eval σ φ := by
    simp only [flipFormula,CNF.eval,List.all_map]
    congr 1
    funext c
    simp only [Function.comp_apply,Clause.eval,List.any_map]
    congr 1
    funext l
    exact eval_lit_flip flip σ l
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨fun i => xor (σ i) (flip i),?_⟩
    have h' := h (fun i => xor (σ i) (flip i))
    have hf : (fun i => xor (xor (σ i) (flip i)) (flip i)) = σ := by
      funext i
      cases σ i <;> cases flip i <;> rfl
    rwa [hf,hσ,eq_comm] at h'
  · rintro ⟨σ,hσ⟩
    exact ⟨fun i => xor (σ i) (flip i),(h σ).trans hσ⟩

private theorem positivity (flip : Assignment) (l : Literal) :
    (flipLiteral flip l).2 = !(Literal.eval flip l) := by
  simp only [flipLiteral,Literal.eval]
  cases l.2 <;> cases flip l.1 <;> rfl

private theorem no_positive (flip : Assignment) (c : Clause) :
    ((c.map (flipLiteral flip)).filter (fun l => l.2)).length = 0 ↔
      ∀ l ∈ c, Literal.eval flip l = true := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h l hl
    have hp := h (flipLiteral flip l) (List.mem_map_of_mem hl)
    rw [positivity] at hp
    cases he : Literal.eval flip l <;> simp_all
  · intro h l hl
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hl
    rw [positivity,h m hm]
    simp

private theorem clause_pairs (flip : Assignment) (c : Clause) :
    CNF.eval flip (hornPairClauses c) = true ↔
      ((c.map (flipLiteral flip)).filter (fun l => l.2)).length ≤ 1 := by
  induction c with
  | nil => simp [hornPairClauses,CNF.eval]
  | cons l c ih =>
      have htail : CNF.eval flip (hornPairClauses c) = true ↔
          ((c.map (flipLiteral flip)).filter fun l => l.2).length ≤ 1 := ih
      have hhead : CNF.eval flip (c.map (fun m => [l,m])) = true ↔
          (Literal.eval flip l = true ∨
            ((c.map (flipLiteral flip)).filter (fun l => l.2)).length = 0) := by
        cases h : Literal.eval flip l
        · simp only [h,Bool.false_eq_true,false_or]
          rw [no_positive]
          simp [CNF.eval,Clause.eval,h,List.all_eq_true]
        · simp [CNF.eval,Clause.eval,h]
      simp only [hornPairClauses,CNF.eval,List.all_append,Bool.and_eq_true] at hhead htail ⊢
      rw [hhead,htail,List.map_cons,List.filter_cons,positivity]
      cases h : Literal.eval flip l
      · simp only [Bool.false_eq_true,false_or,Bool.not_false,ite_true,List.length_cons]
        omega
      · simp only [true_or,true_and,Bool.not_true,Bool.false_eq_true,ite_false]

theorem pair_constraints_truth (φ : CNF) (flip : Assignment) :
    CNF.eval flip (hornRenamingConstraints φ) = true ↔
      ∀ c ∈ flipFormula flip φ, (c.filter fun l => l.2).length ≤ 1 := by
  simp only [hornRenamingConstraints,flipFormula,CNF.eval,List.all_flatMap]
  rw [List.all_eq_true]
  constructor
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (clause_pairs flip d).mp (h d hd)
  · intro h c hc
    exact (clause_pairs flip c).mpr (h _ (List.mem_map_of_mem hc))

theorem pair_constraints_width (φ : CNF) : IsKCNF 2 (hornRenamingConstraints φ) := by
  have hw : ∀ (c : Clause), IsKCNF 2 (hornPairClauses c) := by
    intro c
    induction c with
    | nil => simp [hornPairClauses,IsKCNF]
    | cons l ls ih =>
        intro cl hc
        simp only [hornPairClauses,List.mem_append] at hc
        rcases hc with hc | hc
        · obtain ⟨m,_,rfl⟩ := List.mem_map.mp hc
          simp
        · exact ih _ hc
  intro c hc
  obtain ⟨d,_,hd⟩ := List.mem_flatMap.mp hc
  exact hw d c hd

/-- Satisfiable pair constraints characterize Horn renamability of reference CNF. -/
theorem RenamableHornPairConstraints (φ : CNF) :
    ∃ F : CNF, IsKCNF 2 F ∧ ∀ flip : Assignment,
      CNF.eval flip F = true ↔
        ∀ c ∈ φ, ((c.map (fun l => (l.1, xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1 := by
  refine ⟨hornRenamingConstraints φ,pair_constraints_width φ,fun flip => ?_⟩
  rw [pair_constraints_truth]
  change (∀ c ∈ φ.map (fun c => c.map (flipLiteral flip)), (c.filter fun l => l.2).length ≤ 1) ↔
    ∀ c ∈ φ, ((c.map (fun l => (l.1, xor l.2 (flip l.1)))).filter (fun l => l.2)).length ≤ 1
  constructor
  · intro h c hc
    exact h _ (List.mem_map_of_mem hc)
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact h d hd

end PEqualNP.Outside
