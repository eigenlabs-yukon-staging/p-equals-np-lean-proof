import PEqualNP.Outside.RUPSoundness
import PEqualNP.Library.SearchHelpers.TwoSatStr

namespace PEqualNP.Outside

open PEqualNP.Search PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.SatV

private theorem neg_same (l : Literal) : neg l ≠ l := by
  obtain ⟨i,b⟩ := l
  cases b <;> simp [neg]

private theorem edge_justifies {φ : CNF} {A : Set Literal} {u v : Literal}
    (he : Edge φ u v) (hu : UPForces (clauseSet φ) A u) :
    ∃ c ∈ φ, v ∈ c ∧ ∀ m ∈ c, m ≠ v → UPForces (clauseSet φ) A (negLit m) := by
  obtain ⟨c,hc,hm⟩ := he
  rcases (mem_forced_single c u v).mp hm with ⟨rfl,_⟩ | ⟨l,hl,rfl⟩
  · exact ⟨[v],hc,by simp,fun _ hm hn => (hn (List.mem_singleton.mp hm)).elim⟩
  · rcases hl with rfl | rfl
    · refine ⟨[l,v],hc,by simp,fun m hm hn => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hu
      · exact (hn (List.mem_singleton.mp hm)).elim
    · refine ⟨[v,l],hc,by simp,fun m hm hn => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (hn rfl).elim
      · rw [List.mem_singleton.mp hm]
        exact hu

private theorem reach_forces {φ : CNF} {A : Set Literal} {u v : Literal}
    (h : Reach φ u v) (hu : UPForces (clauseSet φ) A u) : UPForces (clauseSet φ) A v := by
  induction h with
  | refl => exact hu
  | tail _ he ih =>
      obtain ⟨c,hc,hl,hrest⟩ := edge_justifies he ih
      exact .unit (D := c.toFinset) ⟨c,hc,rfl⟩ (List.mem_toFinset.mpr hl)
        (fun m hm hne => hrest m (List.mem_toFinset.mp hm) hne)

private theorem reach_rup {φ : CNF} {u : Literal} (h : Reach φ u (neg u)) :
    IsRUP (clauseSet φ) ([neg u] : Clause).toFinset := by
  let A := negLit '' (↑([neg u] : Clause).toFinset : Set Literal)
  have hA : u ∈ A := by
    refine ⟨neg u,by simp,?_⟩
    exact PEqualNP.Library.SearchHelpers.TwoSat.neg_neg u
  obtain hm | ⟨v,hv,he⟩ := h.cases_tail
  · exact (neg_same u hm).elim
  · obtain ⟨c,hc,hl,hrest⟩ := edge_justifies he (reach_forces hv (.hyp hA))
    refine ⟨c.toFinset,⟨c,hc,rfl⟩,fun l hl' => ?_⟩
    by_cases hl'' : l = neg u
    · rw [hl'']
      exact .hyp (by change neg (neg u) ∈ A; rw [PEqualNP.Library.SearchHelpers.TwoSat.neg_neg]; exact hA)
    · exact hrest l (List.mem_toFinset.mp hl') hl''

private theorem forces_mono {Γ Δ : Set FinClause} {A : Set Literal} (hs : Γ ⊆ Δ)
    {l : Literal} (h : UPForces Γ A l) : UPForces Δ A l := by
  induction h with
  | hyp h => exact .hyp h
  | unit hc hl _ ih => exact .unit (hs hc) hl ih

private theorem rup_mono {Γ Δ : Set FinClause} {c : FinClause} (hs : Γ ⊆ Δ)
    (h : IsRUP Γ c) : IsRUP Δ c := by
  obtain ⟨d,hd,h⟩ := h
  exact ⟨d,hs hd,fun l hl => forces_mono hs (h l hl)⟩

private theorem append_inc (φ ρ : CNF) : clauseSet φ ⊆ clauseSet (φ ++ ρ) := by
  rintro d ⟨c,hc,rfl⟩
  exact ⟨c,List.mem_append_left _ hc,rfl⟩

theorem empty_rup {φ : CNF} (h : [] ∈ φ) : IsRUPRun (clauseSet φ) (([[]] : CNF).map List.toFinset) := by
  apply (rup_run_cons φ [] []).mpr
  constructor
  · refine ⟨∅,⟨[],by simpa using h,rfl⟩,?_⟩
    simp
  · exact .nil

theorem conflict_trace {φ : CNF} (u : Literal)
    (h1 : Reach φ u (neg u)) (h2 : Reach φ (neg u) u) :
    IsRUPRun (clauseSet φ) (([[],[neg u],[u]] : CNF).map List.toFinset) := by
  have h2' : Reach φ (neg u) (neg (neg u)) := by simpa only [PEqualNP.Library.SearchHelpers.TwoSat.neg_neg] using h2
  have hlearn : IsRUPRun (clauseSet φ) (([[u]] : CNF).map List.toFinset) := by
    apply (rup_run_cons φ [] [u]).mpr
    have he := reach_rup h2'
    rw [PEqualNP.Library.SearchHelpers.TwoSat.neg_neg] at he
    exact ⟨by simpa using he,.nil⟩
  have hneg : IsRUPRun (clauseSet φ) (([[neg u],[u]] : CNF).map List.toFinset) := by
    apply (rup_run_cons φ [[u]] [neg u]).mpr
    exact ⟨rup_mono (append_inc φ [[u]]) (reach_rup h1),hlearn⟩
  apply (rup_run_cons φ [[neg u],[u]] []).mpr
  refine ⟨⟨([u] : Clause).toFinset,
    ⟨[u],List.mem_append_right _ (by simp),rfl⟩,?_⟩,hneg⟩
  intro l hl
  have he : l = u := List.mem_singleton.mp (List.mem_toFinset.mp hl)
  subst l
  refine .unit (D := ([neg u] : Clause).toFinset) ⟨[neg u],List.mem_append_right _ (by simp),rfl⟩
    (by simp [negLit,neg]) ?_
  intro m hm hn
  have he : m = neg u := List.mem_singleton.mp (List.mem_toFinset.mp hm)
  exact (hn (by simpa only [negLit,neg] using he)).elim

private theorem in_clause_size (l : Literal) (c : Clause) (hc : l ∈ c) :
    (encodeLiteral l).length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp at hc
  | cons m c ih =>
      have he : encodeClause (m :: c) = encodeLiteral m ++ encodeClause c := by simp [encodeClause]
      rw [he,List.length_append]
      rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · exact (ih hc).trans (Nat.le_add_left _ _)

theorem in_formula_size (φ : CNF) (c : Clause) (l : Literal) (hc : c ∈ φ) (hl : l ∈ c) :
    (encodeLiteral l).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp at hc
  | cons d ds ih =>
      have he : encodeCNF (d :: ds) = encodeClause d ++ encodeCNF ds := by simp [encodeCNF]
      rw [he,List.length_append]
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (in_clause_size l c hl).trans (Nat.le_add_right _ _)
      · exact (ih hc).trans (Nat.le_add_left _ _)

theorem conflict_trace_size (u : Literal) :
    (encodeCNF [[],[neg u],[u]]).length = 2*(encodeLiteral u).length+6 := by
  simp [encodeCNF,encodeClause,encodeLiteral_eq,neg]
  omega

theorem twoSat_conflict (φ : CNF) (hw : IsKCNF 2 φ) (h0 : [] ∉ φ) (hu : ¬ Satisfiable φ) :
    ∃ c ∈ φ, ∃ l ∈ c, Reach φ l (neg l) ∧ Reach φ (neg l) l := by
  classical
  have hw' (c : Clause) (hc : c ∈ φ) : c.length = 1 ∨ c.length = 2 := by
    have hh := hw c hc
    have hp : 0 < c.length := by
      by_contra h
      have hel : c.length = 0 := by omega
      exact h0 (List.length_eq_zero_iff.mp hel ▸ hc)
    omega
  have h := (sat_iff hw' (rounds_le φ)).not.mp hu
  push Not at h
  obtain ⟨c,hc,l,hl,h1,h2⟩ := h
  exact ⟨c,hc,l,hl,clos_sound h1,clos_sound h2⟩

/-- Unsatisfiable width-two formulas admit a newest-first RUP refutation
using at most three clauses and at most twice the input size plus six bits. -/
theorem TwoSATShortRUP (φ : CNF) (hw : IsKCNF 2 φ) :
    ¬Satisfiable φ ↔
      ∃ ρ : CNF, ρ.length ≤ 3 ∧ (encodeCNF ρ).length ≤ 2*(encodeCNF φ).length+6 ∧
        IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map fun c => c.toFinset) ∧
        [] ∈ ρ := by
  constructor
  · intro hu
    by_cases h : [] ∈ φ
    · refine ⟨[[]],by decide,?_,empty_rup h,by simp⟩
      have h2 : (encodeCNF ([[]] : CNF)).length = 2 := rfl
      omega
    · obtain ⟨c,hc,l,hl,h1,h2⟩ := twoSat_conflict φ hw h hu
      refine ⟨[[],[neg l],[l]],by simp,?_,conflict_trace l h1 h2,by simp⟩
      rw [conflict_trace_size]
      have hsize := in_formula_size φ c l hc hl
      omega
  · rintro ⟨ρ,_,_,hr,he⟩
    exact rup_run_refutes φ ρ hr he

end PEqualNP.Outside
