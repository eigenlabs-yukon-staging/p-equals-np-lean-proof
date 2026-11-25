import PEqualNP.Outside.RUPSoundness

namespace PEqualNP.Outside

open PEqualNP.Search

private theorem horn_positive_unique (c : Clause) (h : (c.filter (fun l => l.2)).length ≤ 1)
    {l m : Literal} (hl : l ∈ c) (hm : m ∈ c) (hl' : l.2 = true) (hm' : m.2 = true) : l = m := by
  have h1 : l ∈ c.filter (fun l => l.2) := List.mem_filter.mpr ⟨hl,hl'⟩
  have h2 : m ∈ c.filter (fun l => l.2) := List.mem_filter.mpr ⟨hm,hm'⟩
  generalize hp : c.filter (fun l => l.2) = p at h h1 h2
  cases p with
  | nil => simp at h1
  | cons a p =>
      cases p with
      | nil => exact (List.mem_singleton.mp h1).trans (List.mem_singleton.mp h2).symm
      | cons a' p => simp at h

/-- Every unsatisfiable Horn CNF has a reverse-unit-propagation refutation
consisting of the single empty learned clause. -/
theorem HornUnitRefutation (φ : CNF) (hHorn : ∀ c ∈ φ, (c.filter (fun l => l.2)).length ≤ 1) :
    ¬Satisfiable φ ↔
      IsRUP {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} ∅ := by
  classical
  let Γ := clauseSet φ
  change ¬Satisfiable φ ↔ IsRUP Γ ∅
  constructor
  · intro hu
    by_contra hrup
    let positive := fun x : ℕ => UPForces Γ ∅ (x,true)
    let σ : Assignment := fun x => @decide (positive x) (Classical.propDecidable _)
    apply hu
    refine ⟨σ,List.all_eq_true.mpr (fun c hc => ?_)⟩
    by_cases hn : ∃ m ∈ c, m.2 = false ∧ ¬ positive m.1
    · obtain ⟨m,hm,hs,hneg⟩ := hn
      have hv : σ m.1 = false := decide_eq_false hneg
      exact List.any_eq_true.mpr ⟨m,hm,by simp [Literal.eval,hv,hs]⟩
    · have hneg (m : Literal) (hm : m ∈ c) (hs : m.2 = false) : UPForces Γ ∅ (negLit m) := by
        have hp : positive m.1 := by
          by_contra he
          exact hn ⟨m,hm,hs,he⟩
        have hm' : negLit m = (m.1,true) := by simp [negLit,hs]
        rw [hm']
        exact hp
      by_cases ht : ∃ l ∈ c, l.2 = true
      · obtain ⟨l,hl,he⟩ := ht
        have hf : UPForces Γ ∅ l := by
          refine .unit (D := c.toFinset) ⟨c,hc,rfl⟩ (List.mem_toFinset.mpr hl) ?_
          intro m hm hne
          have hmem := List.mem_toFinset.mp hm
          have hn' : m.2 ≠ true := fun hh =>
            hne (horn_positive_unique c (hHorn c hc) hl hmem he hh).symm
          exact hneg m hmem (Bool.eq_false_iff.mpr hn')
        have hl' : l = (l.1,true) := Prod.ext rfl he
        have hPos : positive l.1 := hl' ▸ hf
        have hs : σ l.1 = true := decide_eq_true hPos
        exact List.any_eq_true.mpr ⟨l,hl,by simp [Literal.eval,hs,he]⟩
      · exfalso
        apply hrup
        refine ⟨c.toFinset,⟨c,hc,rfl⟩,fun l hl => ?_⟩
        have hm := List.mem_toFinset.mp hl
        have he : l.2 = false := Bool.eq_false_iff.mpr (fun h => ht ⟨l,hm,h⟩)
        simpa using hneg l hm he
  · intro hr
    apply rup_run_refutes φ [[]] _ (by simp)
    apply (rup_run_cons φ [] []).mpr
    exact ⟨by simpa using hr,.nil⟩

end PEqualNP.Outside
