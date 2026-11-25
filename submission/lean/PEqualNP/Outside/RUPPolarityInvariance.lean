import PEqualNP.Outside.RUPSoundness

namespace PEqualNP.Outside

open PEqualNP.Search

private def flipLit (r : Assignment) (l : Literal) : Literal := (l.1,xor l.2 (r l.1))

private theorem flip_invol (r : Assignment) : Function.Involutive (flipLit r) := by
  intro l
  rcases l with ⟨i,b⟩
  cases b <;> cases h : r i <;> simp [flipLit,h]

private theorem flip_neg (r : Assignment) (l : Literal) :
    flipLit r (negLit l) = negLit (flipLit r l) := by
  rcases l with ⟨i,b⟩
  cases b <;> cases h : r i <;> simp [flipLit,negLit,h]

private theorem force_flip (r : Assignment) {Γ : Set FinClause} {A : Set Literal} {l : Literal}
    (h : UPForces Γ A l) :
    UPForces (Finset.image (flipLit r) '' Γ) (flipLit r '' A) (flipLit r l) := by
  induction h with
  | hyp h => exact .hyp ⟨_,h,rfl⟩
  | @unit c l hc hl _ ih =>
      have hC : c.image (flipLit r) ∈ Finset.image (flipLit r) '' Γ := ⟨c,hc,rfl⟩
      refine UPForces.unit (D := c.image (flipLit r)) hC (Finset.mem_image.mpr ⟨l,hl,rfl⟩) ?_
      intro l' hl' hne
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl'
      have hml : m ≠ l := fun e => hne (congrArg (flipLit r) e)
      rw [← flip_neg]
      exact ih m hm hml

private theorem flip_assumptions (r : Assignment) (c : FinClause) :
    flipLit r '' (negLit '' (↑c : Set Literal)) =
      negLit '' (↑(c.image (flipLit r)) : Set Literal) := by
  ext l
  constructor
  · rintro ⟨m,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨flipLit r a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,(flip_neg r a).symm⟩
  · rintro ⟨m,hm,rfl⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
    exact ⟨negLit a,⟨a,ha,rfl⟩,flip_neg r a⟩

private theorem rup_flip (r : Assignment) {Γ : Set FinClause} {c : FinClause} (h : IsRUP Γ c) :
    IsRUP (Finset.image (flipLit r) '' Γ) (c.image (flipLit r)) := by
  obtain ⟨d,hd,hf⟩ := h
  refine ⟨d.image (flipLit r),⟨d,hd,rfl⟩,fun m hm => ?_⟩
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hm
  rw [← flip_assumptions,← flip_neg]
  exact force_flip r (hf l hl)

private theorem flip_clause_invol (r : Assignment) (c : FinClause) :
    (c.image (flipLit r)).image (flipLit r) = c := by
  ext l
  constructor
  · intro h
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    rw [flip_invol r n]
    exact hn
  · intro h
    exact Finset.mem_image.mpr ⟨flipLit r l,Finset.mem_image.mpr ⟨l,h,rfl⟩,flip_invol r l⟩

private theorem flip_formula_invol (r : Assignment) (Γ : Set FinClause) :
    Finset.image (flipLit r) '' (Finset.image (flipLit r) '' Γ) = Γ := by
  ext c
  constructor
  · rintro ⟨d,⟨e,he,rfl⟩,rfl⟩
    simpa only [flip_clause_invol] using he
  · intro hc
    exact ⟨c.image (flipLit r),⟨c,hc,rfl⟩,flip_clause_invol r c⟩

/-- Reverse unit propagation is invariant under an arbitrary, consistent
change of variable polarities, including the candidate clause. -/
theorem RUPPolarityInvariance (r : Assignment) (Γ : Set (PEqualNP.ProofComplexity.Clause ℕ))
    (c : PEqualNP.ProofComplexity.Clause ℕ) :
    let f := fun l : Literal => (l.1,xor l.2 (r l.1))
    IsRUP (Finset.image f '' Γ) (c.image f) ↔ IsRUP Γ c := by
  change IsRUP (Finset.image (flipLit r) '' Γ) (c.image (flipLit r)) ↔ IsRUP Γ c
  constructor
  · intro h
    have hf := rup_flip r h
    rwa [flip_formula_invol,flip_clause_invol] at hf
  · exact rup_flip r

private theorem finset_list_flip (r : Assignment) (c : Clause) :
    (c.map (flipLit r)).toFinset = c.toFinset.image (flipLit r) := by
  ext l
  simp only [List.mem_toFinset,Finset.mem_image,List.mem_map]

theorem clauseSet_flip (r : Assignment) (φ : CNF) :
    clauseSet (φ.map (fun c => c.map (fun l => (l.1,xor l.2 (r l.1))))) = Finset.image (flipLit r) '' clauseSet φ := by
  change clauseSet (φ.map (fun c => c.map (flipLit r))) = _
  ext c
  constructor
  · rintro ⟨d,hd,rfl⟩
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hd
    exact ⟨f.toFinset,⟨f,hf,rfl⟩,(finset_list_flip r f).symm⟩
  · rintro ⟨d,⟨f,hf,rfl⟩,rfl⟩
    exact ⟨f.map (flipLit r),List.mem_map.mpr ⟨f,hf,rfl⟩,finset_list_flip r f⟩

end PEqualNP.Outside
