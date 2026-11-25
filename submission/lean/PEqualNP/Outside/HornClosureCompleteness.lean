import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.Search

def hornAssignment (s : Finset ℕ) : Assignment := fun i => decide (i ∈ s)

def HornClause (c : Clause) : Prop := (c.filter fun l => l.2).length ≤ 1

def hornStep (c : Clause) (s : Finset ℕ) : Finset ℕ :=
  if c.eval (hornAssignment s) then s
  else ((c.filter fun l => l.2).head?).elim s (fun l => insert l.1 s)

def hornSweep (φ : CNF) (s : Finset ℕ) : Finset ℕ := φ.foldl (fun s c => hornStep c s) s

def formulaVars (φ : CNF) : Finset ℕ := ((φ.flatMap id).map Prod.fst).toFinset

private theorem assignment_true (s : Finset ℕ) (i : ℕ) : hornAssignment s i = true ↔ i ∈ s := by
  simp [hornAssignment]

private theorem clause_eval (c : Clause) (σ : Assignment) :
    c.eval σ = true ↔ ∃ l ∈ c, σ l.1 = l.2 := by
  simp only [Clause.eval,List.any_eq_true,Literal.eval,beq_iff_eq]

private theorem formula_eval (φ : CNF) (σ : Assignment) :
    φ.eval σ = true ↔ ∀ c ∈ φ, c.eval σ = true := by
  simp only [CNF.eval,List.all_eq_true]

private theorem head_mem {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l <;> simp_all

private theorem step_extends (c : Clause) (s : Finset ℕ) : s ⊆ hornStep c s := by
  unfold hornStep
  split
  · exact Finset.Subset.refl _
  · cases (c.filter fun l => l.2).head? <;> simp

private theorem step_inside (c : Clause) (s V : Finset ℕ) (hs : s ⊆ V)
    (hc : ∀ l ∈ c, l.1 ∈ V) : hornStep c s ⊆ V := by
  unfold hornStep
  split
  · exact hs
  · cases h : (c.filter fun l => l.2).head? with
    | none => exact hs
    | some l =>
        have hl := (List.mem_filter.mp (head_mem h)).1
        exact Finset.insert_subset_iff.mpr ⟨hc l hl, hs⟩

private theorem must_force (c : Clause) (s : Finset ℕ) (hHorn : HornClause c)
    (σ : Assignment) (hs : ∀ i ∈ s, σ i = true)
    (hc : c.eval σ = true) (hcur : c.eval (hornAssignment s) = false) :
    ∃ l : Literal, (c.filter fun l => l.2).head? = some l ∧ σ l.1 = true ∧ l.1 ∉ s := by
  obtain ⟨l,hl,he⟩ := (clause_eval c σ).mp hc
  have ht : l.2 = true := by
    cases h : l.2 with
    | true => rfl
    | false =>
        have hn : l.1 ∉ s := by
          intro hi
          rw [hs _ hi,h] at he
          contradiction
        have had : hornAssignment s l.1 = l.2 := by simp [hornAssignment,hn,h]
        have := (clause_eval c (hornAssignment s)).mpr ⟨l,hl,had⟩
        simp_all
  have hmem : l ∈ c.filter (fun l => l.2) := List.mem_filter.mpr ⟨hl,ht⟩
  have hhead : (c.filter fun l => l.2).head? = some l := by
    generalize hls : c.filter (fun l => l.2) = ls at hmem
    have hlen : ls.length ≤ 1 := by
      have h := hHorn
      unfold HornClause at h
      rwa [hls] at h
    cases ls with
    | nil => simp at hmem
    | cons a rest =>
        have hc : rest.length + 1 ≤ 1 := hlen
        have he : rest = [] := List.length_eq_zero_iff.mp (by omega)
        subst rest
        have hla := List.mem_singleton.mp hmem
        simp [hla]
  have hn : l.1 ∉ s := by
    intro hi
    have ha := (assignment_true s l.1).mpr hi
    have := (clause_eval c (hornAssignment s)).mpr ⟨l,hl,ha.trans ht.symm⟩
    simp_all
  exact ⟨l,hhead,he.trans ht,hn⟩

private theorem step_model (c : Clause) (s : Finset ℕ) (hHorn : HornClause c)
    (σ : Assignment) (hs : ∀ i ∈ s, σ i = true) (hc : c.eval σ = true) :
    ∀ i ∈ hornStep c s, σ i = true := by
  by_cases h : c.eval (hornAssignment s) = true
  · simpa [hornStep,h] using hs
  · have hfalse : c.eval (hornAssignment s) = false := Bool.eq_false_iff.mpr h
    obtain ⟨l,hl,hval,_⟩ := must_force c s hHorn σ hs hc hfalse
    intro i hi
    simp only [hornStep,hfalse,Bool.false_eq_true,ite_false,hl,Option.elim_some,Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hval
    · exact hs i hi

private theorem step_grows (c : Clause) (s : Finset ℕ) (hHorn : HornClause c)
    (σ : Assignment) (hs : ∀ i ∈ s, σ i = true)
    (hc : c.eval σ = true) (hcur : c.eval (hornAssignment s) = false) :
    s ⊂ hornStep c s := by
  obtain ⟨l,hl,_,hn⟩ := must_force c s hHorn σ hs hc hcur
  rw [show hornStep c s = insert l.1 s by simp [hornStep,hcur,hl]]
  exact Finset.ssubset_insert hn

private theorem sweep_extends (φ : CNF) (s : Finset ℕ) : s ⊆ hornSweep φ s := by
  induction φ generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons c φ ih =>
      exact (step_extends c s).trans (ih (hornStep c s))

private theorem sweep_inside (φ : CNF) (s V : Finset ℕ) (hs : s ⊆ V)
    (hc : ∀ c ∈ φ, ∀ l ∈ c, l.1 ∈ V) : hornSweep φ s ⊆ V := by
  induction φ generalizing s with
  | nil => exact hs
  | cons c φ ih =>
      exact ih _ (step_inside c s V hs (hc c List.mem_cons_self))
        (fun d hd => hc d (List.mem_cons_of_mem _ hd))

private theorem sweep_model (φ : CNF) (s : Finset ℕ) (hHorn : ∀ c ∈ φ, HornClause c)
    (σ : Assignment) (hs : ∀ i ∈ s, σ i = true) (hc : φ.eval σ = true) :
    ∀ i ∈ hornSweep φ s, σ i = true := by
  induction φ generalizing s with
  | nil => exact hs
  | cons c φ ih =>
      have hh := (formula_eval (c :: φ) σ).mp hc
      exact ih _ (fun d hd => hHorn d (List.mem_cons_of_mem _ hd))
        (step_model c s (hHorn c List.mem_cons_self) σ hs (hh c List.mem_cons_self))
        ((formula_eval φ σ).mpr fun d hd => hh d (List.mem_cons_of_mem _ hd))

private theorem sweep_stable (φ : CNF) (s : Finset ℕ) (h : φ.eval (hornAssignment s) = true) :
    hornSweep φ s = s := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      have h' := (formula_eval (c :: φ) (hornAssignment s)).mp h
      change hornSweep φ (hornStep c s) = s
      rw [show hornStep c s = s by simp [hornStep,h' c List.mem_cons_self]]
      exact ih ((formula_eval φ (hornAssignment s)).mpr fun d hd => h' d (List.mem_cons_of_mem _ hd))

private theorem sweep_grows (φ : CNF) (s : Finset ℕ)
    (hHorn : ∀ c ∈ φ, HornClause c) (σ : Assignment) (hs : ∀ i ∈ s, σ i = true)
    (hm : φ.eval σ = true) (hcur : φ.eval (hornAssignment s) = false) :
    s ⊂ hornSweep φ s := by
  induction φ generalizing s with
  | nil => simp [CNF.eval] at hcur
  | cons c φ ih =>
      have hc := (formula_eval (c :: φ) σ).mp hm
      change s ⊂ hornSweep φ (hornStep c s)
      by_cases he : c.eval (hornAssignment s) = true
      · rw [show hornStep c s = s by simp [hornStep,he]]
        have ht : CNF.eval (hornAssignment s) φ = false := by
          simpa [CNF.eval,he] using hcur
        exact ih _ (fun d hd => hHorn d (List.mem_cons_of_mem _ hd)) hs
          ((formula_eval φ σ).mpr fun d hd => hc d (List.mem_cons_of_mem _ hd)) ht
      · exact (step_grows c s (hHorn c List.mem_cons_self) σ hs
          (hc c List.mem_cons_self) (Bool.eq_false_iff.mpr he)).trans_subset
          (sweep_extends φ _)

private theorem vars_mem (φ : CNF) (c : Clause) (hc : c ∈ φ) (l : Literal) (hl : l ∈ c) :
    l.1 ∈ formulaVars φ := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l,List.mem_flatMap.mpr ⟨c,hc,hl⟩,rfl⟩)

private theorem iter_invariant (φ : CNF) (hHorn : ∀ c ∈ φ, HornClause c)
    (σ : Assignment) (hSat : φ.eval σ = true) (n : ℕ) :
    (hornSweep φ)^[n] ∅ ⊆ formulaVars φ ∧
      (∀ i ∈ (hornSweep φ)^[n] ∅, σ i = true) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨sweep_inside φ _ _ ih.1 (fun c hc l hl => vars_mem φ c hc l hl),
        sweep_model φ _ hHorn σ ih.2 hSat⟩

private theorem iter_growth_until (φ : CNF) (hHorn : ∀ c ∈ φ, HornClause c)
    (σ : Assignment) (hSat : φ.eval σ = true) (n : ℕ)
    (hn : φ.eval (hornAssignment ((hornSweep φ)^[n] ∅)) = false) :
    n ≤ ((hornSweep φ)^[n] ∅).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply'] at hn ⊢
      let s := (hornSweep φ)^[n] ∅
      have hf : φ.eval (hornAssignment s) = false := by
        cases ht : φ.eval (hornAssignment s) with
        | false => rfl
        | true =>
            have hfix := sweep_stable φ s ht
            change φ.eval (hornAssignment (hornSweep φ s)) = false at hn
            rw [hfix,ht] at hn
            contradiction
      have hs := (iter_invariant φ hHorn σ hSat n).2
      have hg := sweep_grows φ s hHorn σ hs hSat hf
      have hcard := Finset.card_lt_card hg
      exact (ih hf).trans_lt hcard

theorem horn_sweep_decides (φ : CNF) (hHorn : ∀ c ∈ φ, HornClause c)
    (n : ℕ) (hn : (formulaVars φ).card ≤ n) :
    Satisfiable φ ↔ φ.eval (hornAssignment ((hornSweep φ)^[n] ∅)) = true := by
  constructor
  · rintro ⟨σ,hSat⟩
    let s := (hornSweep φ)^[n] ∅
    cases he : φ.eval (hornAssignment s) with
    | true => rfl
    | false =>
        have hlow := iter_growth_until φ hHorn σ hSat n he
        have hs := (iter_invariant φ hHorn σ hSat n).2
        have hg := Finset.card_lt_card (sweep_grows φ s hHorn σ hs hSat he)
        have hbound := (iter_invariant φ hHorn σ hSat (n+1)).1
        rw [Function.iterate_succ_apply'] at hbound
        have h := Finset.card_le_card hbound
        change n ≤ s.card at hlow
        change (hornSweep φ s).card ≤ (formulaVars φ).card at h
        omega
  · intro h
    exact ⟨_,h⟩

/-- A Horn CNF with a satisfying assignment has a least model in its finite variable set. -/
theorem HornClosureCompleteness (φ : CNF)
    (hHorn : ∀ c ∈ φ, (c.filter (fun l => l.2)).length ≤ 1)
    (hSat : Satisfiable φ) :
    ∃ s : Finset ℕ, CNF.eval (fun i => decide (i ∈ s)) φ = true ∧
      (∀ i ∈ s, ∃ c ∈ φ, ∃ l ∈ c, l.1 = i) ∧
      ∀ σ : Assignment, CNF.eval σ φ = true → ∀ i ∈ s, σ i = true := by
  let n := (formulaVars φ).card
  let s := (hornSweep φ)^[n] ∅
  refine ⟨s,(horn_sweep_decides φ hHorn n le_rfl).mp hSat, ?_, ?_⟩
  · intro i hi
    obtain ⟨σ,hσ⟩ := hSat
    have hv := (iter_invariant φ hHorn σ hσ n).1 hi
    obtain ⟨l,hl,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨c,hc,hl⟩ := List.mem_flatMap.mp hl
    exact ⟨c,hc,l,hl,he⟩
  · intro σ hσ
    exact (iter_invariant φ hHorn σ hσ n).2

end PEqualNP.Outside
