import PEqualNP.Outside.FiniteListFixedPoint
import PEqualNP.Outside.UnitPropagationCorrect

namespace PEqualNP.Outside

open PEqualNP.Search
open PEqualNP.ProofComplexity (IsDerivation IsRefutation IsResolvent)

def resolutionLine (φ old : CNF) (c : Clause) : Prop :=
  (∃ d ∈ φ, d.toFinset = c.toFinset) ∨
  ∃ a ∈ old, ∃ b ∈ old, IsResolvent a.toFinset b.toFinset c.toFinset

noncomputable def resolutionRound (φ U L : CNF) : CNF :=
  U.filter (fun c => @decide (resolutionLine φ L c) (Classical.propDecidable _))

theorem mem_resolutionRound (φ U L : CNF) (c : Clause) :
    c ∈ resolutionRound φ U L ↔ c ∈ U ∧ resolutionLine φ L c := by
  classical
  simp [resolutionRound]

private theorem line_mono {φ L M : CNF} {c : Clause} (h : L ⊆ M)
    (hl : resolutionLine φ L c) : resolutionLine φ M c := by
  rcases hl with ha | ⟨a,ha,b,hb,hr⟩
  · exact Or.inl ha
  · exact Or.inr ⟨a,h ha,b,h hb,hr⟩

noncomputable def resolutionKnown (φ U : CNF) (n : ℕ) : CNF := (resolutionRound φ U)^[n] []

theorem known_step (φ U : CNF) (n : ℕ) :
    resolutionKnown φ U (n+1) = resolutionRound φ U (resolutionKnown φ U n) :=
  Function.iterate_succ_apply' _ _ _

noncomputable def resolutionTrace (φ U : CNF) : ℕ → CNF
  | 0 => []
  | n+1 => resolutionKnown φ U (n+1) ++ resolutionTrace φ U n

theorem known_in_trace (φ U : CNF) (n : ℕ) : resolutionKnown φ U n ⊆ resolutionTrace φ U n := by
  cases n with
  | zero => exact fun _ h => h
  | succ n => exact fun _ h => List.mem_append_left _ h

private theorem trace_subset (φ U : CNF) (n : ℕ) : resolutionTrace φ U n ⊆ U := by
  induction n with
  | zero => simp [resolutionTrace]
  | succ n ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rw [known_step] at hc
        exact (mem_resolutionRound _ _ _ _).mp hc |>.1
      · exact ih hc

private theorem add_round (φ old previous next : CNF)
    (hprev : IsDerivation (clauseSet φ) (previous.map List.toFinset))
    (hOld : old ⊆ previous)
    (hline : ∀ c ∈ next, resolutionLine φ old c) :
    IsDerivation (clauseSet φ) ((next ++ previous).map List.toFinset) := by
  induction next with
  | nil => exact hprev
  | cons c cs ih =>
      have hr : IsDerivation (clauseSet φ) ((cs ++ previous).map List.toFinset) :=
        ih (fun d hd => hline d (List.mem_cons_of_mem _ hd))
      have hc := hline c List.mem_cons_self
      rcases hc with hAx | ⟨a,ha,b,hb,he⟩
      · exact .ax hr hAx
      · exact .res hr (List.mem_map_of_mem (List.mem_append_right _ (hOld ha)))
          (List.mem_map_of_mem (List.mem_append_right _ (hOld hb))) he

theorem resolutionTrace_derives (φ U : CNF) (n : ℕ) :
    IsDerivation (clauseSet φ) ((resolutionTrace φ U n).map List.toFinset) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
      change IsDerivation _ ((resolutionKnown φ U (n+1) ++ resolutionTrace φ U n).map List.toFinset)
      apply add_round φ (resolutionKnown φ U n) _ _ ih (known_in_trace φ U n)
      intro c hc
      rw [known_step] at hc
      exact (mem_resolutionRound _ _ _ _).mp hc |>.2

private theorem derivation_support (φ : CNF) {π : List FinClause}
    (h : IsDerivation (clauseSet φ) π) : ∀ c ∈ π, ∀ l ∈ c, l ∈ φ.flatMap id := by
  induction h with
  | nil => simp
  | @ax π C _ hc ih =>
      intro d hd l hl
      rcases List.mem_cons.mp hd with rfl | hd
      · obtain ⟨c,hc,rfl⟩ := hc
        exact List.mem_flatMap.mpr ⟨c,hc,List.mem_toFinset.mp hl⟩
      · exact ih d hd l hl
  | @res π C D R _ hC hD hr ih =>
      intro c hc l hl
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨v,_,_,rfl⟩ := hr
        rcases Finset.mem_union.mp hl with hl | hl
        · exact ih C hC l (Finset.mem_erase.mp hl).2
        · exact ih D hD l (Finset.mem_erase.mp hl).2
      · exact ih c hc l hl

theorem resolutionKnown_complete (φ U : CNF) (k n : ℕ)
    (hU : ∀ c : Clause, c.length ≤ k → c ⊆ φ.flatMap id → c ∈ U) (hn : U.length ≤ n)
    {π : List FinClause} (hπ : IsDerivation (clauseSet φ) π) (hw : ∀ c ∈ π, c.card ≤ k) :
    ∀ c ∈ π, ∃ d ∈ resolutionKnown φ U n, d.toFinset = c := by
  let L := resolutionKnown φ U n
  have hm : ∀ A B : CNF, A ⊆ B → resolutionRound φ U A ⊆ resolutionRound φ U B := by
    intro A B h c hc
    obtain ⟨hm,hv⟩ := (mem_resolutionRound φ U A c).mp hc
    exact (mem_resolutionRound φ U B c).mpr ⟨hm,line_mono h hv⟩
  have hbound : ∀ A : CNF, resolutionRound φ U A ⊆ U := by
    intro A c hc
    exact (mem_resolutionRound φ U A c).mp hc |>.1
  have hf (c : Clause) : c ∈ L ↔ c ∈ U ∧ resolutionLine φ L c :=
    (FiniteListFixedPoint (resolutionRound φ U) U hm hbound n hn c).trans (mem_resolutionRound φ U L c)
  have hstep (C : FinClause) (hW : C.card ≤ k) (hs : ∀ l ∈ C, l ∈ φ.flatMap id)
      (hline : resolutionLine φ L C.toList) : ∃ d ∈ L, d.toFinset = C := by
    refine ⟨C.toList,(hf _).mpr ⟨hU _ ?_ (fun l hl => hs l (Finset.mem_toList.mp hl)),hline⟩,Finset.toList_toFinset _⟩
    rw [Finset.length_toList]
    exact hW
  induction hπ with
  | nil => simp
  | @ax π C hD hC ih =>
      intro c hc
      rcases List.mem_cons.mp hc with he | hc
      · subst c
        apply hstep _ (hw _ List.mem_cons_self)
        · intro l hl
          obtain ⟨d,hd,hEq⟩ := hC
          exact List.mem_flatMap.mpr ⟨d,hd,List.mem_toFinset.mp (hEq.symm ▸ hl)⟩
        · obtain ⟨d,hd,hEq⟩ := hC
          exact Or.inl ⟨d,hd,hEq.trans (Finset.toList_toFinset C).symm⟩
      · exact ih (fun c hc => hw c (List.mem_cons_of_mem _ hc)) c hc
  | @res π A B C hD hA hB hr ih =>
      have hw' : ∀ d ∈ π, Finset.card d ≤ k := fun d hd => hw d (List.mem_cons_of_mem _ hd)
      intro c hc
      rcases List.mem_cons.mp hc with he | hc
      · subst c
        apply hstep C (hw _ List.mem_cons_self)
        · exact derivation_support φ (IsDerivation.res hD hA hB hr) C List.mem_cons_self
        · obtain ⟨a,ha,hEq⟩ := ih hw' A hA
          obtain ⟨b,hb,hEq'⟩ := ih hw' B hB
          right
          refine ⟨a,ha,b,hb,?_⟩
          rw [hEq,hEq',Finset.toList_toFinset]
          exact hr
      · exact ih hw' c hc

theorem resolutionKnown_empty (φ U : CNF) (k n : ℕ)
    (hU : ∀ c : Clause, c ∈ U ↔ c.length ≤ k ∧ c ⊆ φ.flatMap id) (hn : U.length ≤ n) :
    [] ∈ resolutionKnown φ U n ↔
      ∃ π : List FinClause, IsRefutation (clauseSet φ) π ∧ ∀ c ∈ π, c.card ≤ k := by
  constructor
  · intro he
    let π := resolutionTrace φ U n
    refine ⟨π.map List.toFinset,⟨resolutionTrace_derives φ U n,?_⟩,fun d hd => ?_⟩
    · exact List.mem_map.mpr ⟨[],known_in_trace φ U n he,List.toFinset_nil⟩
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
      have h := ((hU c).mp (trace_subset φ U n hc)).1
      exact (List.toFinset_card_le (l := c)).trans h
  · rintro ⟨π,⟨hπ,he⟩,hw⟩
    obtain ⟨c,hc,hEq⟩ := resolutionKnown_complete φ U k n (fun c h1 h2 => (hU c).mpr ⟨h1,h2⟩) hn hπ hw ∅ he
    cases c with
    | nil => exact hc
    | cons l ls =>
        have h : l ∈ (l :: ls).toFinset := List.mem_toFinset.mpr List.mem_cons_self
        rw [hEq] at h
        simp at h

theorem resolutionTrace_width (φ U : CNF) (k n : ℕ)
    (hU : ∀ c ∈ U, List.length c ≤ k) :
    ∀ d ∈ (resolutionTrace φ U n).map List.toFinset, Finset.card d ≤ k := by
  intro d hd
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
  exact (List.toFinset_card_le (l := c)).trans (hU c (trace_subset φ U n hc))

theorem resolutionTrace_empty (φ U : CNF) (k n : ℕ)
    (hU : ∀ c : Clause, c ∈ U ↔ c.length ≤ k ∧ c ⊆ φ.flatMap id) (hn : U.length ≤ n) :
    [] ∈ resolutionTrace φ U n ↔
      ∃ π : List FinClause, IsRefutation (clauseSet φ) π ∧ ∀ c ∈ π, c.card ≤ k := by
  constructor
  · intro he
    have hE : (∅ : FinClause) ∈ (resolutionTrace φ U n).map List.toFinset :=
      List.mem_map.mpr ⟨[],he,List.toFinset_nil⟩
    exact ⟨_,⟨resolutionTrace_derives φ U n,hE⟩,
      resolutionTrace_width φ U k n (fun c hc => ((hU c).mp hc).1)⟩
  · intro h
    exact known_in_trace φ U n ((resolutionKnown_empty φ U k n hU hn).mpr h)

end PEqualNP.Outside
