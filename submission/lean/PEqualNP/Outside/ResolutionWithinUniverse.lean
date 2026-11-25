import PEqualNP.Outside.BoundedResolutionSaturation

namespace PEqualNP.Outside

open PEqualNP.Search
open PEqualNP.ProofComplexity (IsDerivation IsRefutation IsResolvent)

def represented (U : CNF) (d : FinClause) : Prop := ∃ c ∈ U, c.toFinset = d

private theorem line_increasing (φ L M : CNF) (h : L ⊆ M) (c : Clause) :
    resolutionLine φ L c → resolutionLine φ M c := by
  rintro (he | ⟨a,ha,b,hb,hr⟩)
  · exact Or.inl he
  · exact Or.inr ⟨a,h ha,b,h hb,hr⟩

private theorem membership_fixed (φ U : CNF) (n : ℕ) (hn : U.length ≤ n) (c : Clause) :
    c ∈ resolutionKnown φ U n ↔ c ∈ U ∧ resolutionLine φ (resolutionKnown φ U n) c := by
  have hm (L M : CNF) (h : L ⊆ M) : resolutionRound φ U L ⊆ resolutionRound φ U M := by
    intro c hc
    obtain ⟨hm,hq⟩ := (mem_resolutionRound _ _ _ _).mp hc
    exact (mem_resolutionRound _ _ _ _).mpr ⟨hm,line_increasing φ L M h c hq⟩
  have hb (L : CNF) : resolutionRound φ U L ⊆ U := by
    intro d hd
    exact ((mem_resolutionRound _ _ _ _).mp hd).1
  exact (FiniteListFixedPoint (resolutionRound φ U) U hm hb n hn c).trans (mem_resolutionRound _ _ _ _)

private theorem known_covers (φ U : CNF) (n : ℕ) (hn : U.length ≤ n)
    {π : List FinClause} (hr : IsDerivation (clauseSet φ) π)
    (hc : ∀ d ∈ π, represented U d) :
    ∀ d ∈ π, represented (resolutionKnown φ U n) d := by
  let L := resolutionKnown φ U n
  have hd (c : Clause) : c ∈ U → resolutionLine φ L c → c ∈ L :=
    fun hu hr => (membership_fixed φ U n hn c).mpr ⟨hu,hr⟩
  induction hr with
  | nil => simp
  | @ax π C _ hC ih =>
      intro d h
      rcases List.mem_cons.mp h with he | hm
      · subst d
        obtain ⟨a,ha,he⟩ := hc _ List.mem_cons_self
        obtain ⟨b,hb,he'⟩ := hC
        exact ⟨a,hd a ha (Or.inl ⟨b,hb,he'.trans he.symm⟩),he⟩
      · exact ih (fun e he => hc e (List.mem_cons_of_mem _ he)) d hm
  | @res π A B C _ hA hB hR ih =>
      have hh (e : FinClause) (he : e ∈ π) := ih (fun d hd => hc d (List.mem_cons_of_mem _ hd)) e he
      intro d h
      rcases List.mem_cons.mp h with he | he
      · subst d
        obtain ⟨a,ha,hfa⟩ := hh A hA
        obtain ⟨b,hb,hfb⟩ := hh B hB
        obtain ⟨r,hr,hfr⟩ := hc _ List.mem_cons_self
        have hline : resolutionLine φ L r := by
          right
          exact ⟨a,ha,b,hb,by simpa only [hfa,hfb,hfr] using hR⟩
        exact ⟨r,hd r hr hline,hfr⟩
      · exact hh d he

theorem resolutionTrace_subset (φ U : CNF) (n : ℕ) : resolutionTrace φ U n ⊆ U := by
  induction n with
  | zero => simp [resolutionTrace]
  | succ n ih =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rw [known_step] at hc
        exact ((mem_resolutionRound _ _ _ _).mp hc).1
      · exact ih hc

theorem trace_empty_iff (ρ : CNF) : ([] : Clause) ∈ ρ ↔ (∅ : FinClause) ∈ ρ.map List.toFinset := by
  constructor
  · exact fun h => List.mem_map.mpr ⟨[],h,List.toFinset_nil⟩
  · intro h
    obtain ⟨c,hc,he⟩ := List.mem_map.mp h
    cases c with
    | nil => exact hc
    | cons l ls =>
        have hm : l ∈ (l :: ls).toFinset := List.mem_toFinset.mpr List.mem_cons_self
        rw [he] at hm
        simp at hm

theorem trace_within_universe (φ U : CNF) (n : ℕ) (hn : U.length ≤ n) :
    ([] : Clause) ∈ resolutionTrace φ U n ↔
      ∃ π : List FinClause, IsRefutation (clauseSet φ) π ∧ ∀ d ∈ π, represented U d := by
  constructor
  · intro h
    refine ⟨(resolutionTrace φ U n).map List.toFinset,
      ⟨resolutionTrace_derives φ U n,(trace_empty_iff _).mp h⟩,fun d hd => ?_⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    exact ⟨c,resolutionTrace_subset φ U n hc,rfl⟩
  · rintro ⟨π,⟨hr,h0⟩,hU⟩
    obtain ⟨c,hc,he⟩ := known_covers φ U n hn hr hU ∅ h0
    have htrace := known_in_trace φ U n hc
    exact (trace_empty_iff _).mpr (List.mem_map.mpr ⟨c,htrace,he⟩)

end PEqualNP.Outside
