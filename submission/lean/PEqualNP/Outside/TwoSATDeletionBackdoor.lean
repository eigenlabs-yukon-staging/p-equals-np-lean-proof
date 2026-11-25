import PEqualNP.Outside.LowWeightProgress
import PEqualNP.Library.L030

namespace PEqualNP.Outside

open PEqualNP.Search PEqualNP.Library.SearchHelpers

def eraseVariable (x : ℕ) (φ : CNF) : CNF := φ.map (fun c => c.filter (fun l => decide (l.1 ≠ x)))

def eraseVariables (xs : List ℕ) (φ : CNF) : CNF :=
  φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))

def widthTwoBackdoor (k : ℕ) (φ : CNF) : Prop :=
  ∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2 (eraseVariables xs φ)

theorem restrict_sublist_erase (x : ℕ) (b : Bool) {φ ψ : CNF} (h : ψ.Sublist φ) :
    (restrict x b ψ).Sublist (eraseVariable x φ) := by
  exact ((List.filter_sublist : (ψ.filter (fun c => decide ((x,b) ∉ c))).Sublist ψ).trans h).map _

theorem width_sublist {k : ℕ} {φ ψ : CNF} (h : ψ.Sublist φ) (hw : IsKCNF k φ) : IsKCNF k ψ :=
  fun c hc => hw c (h.subset hc)

private theorem erase_nil (φ : CNF) : eraseVariables [] φ = φ := by simp [eraseVariables]

private theorem erase_cons (x : ℕ) (xs : List ℕ) (φ : CNF) :
    eraseVariables (x :: xs) φ = eraseVariables xs (eraseVariable x φ) := by
  unfold eraseVariables eraseVariable
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  dsimp only [Function.comp_apply]
  rw [List.filter_filter]
  apply List.filter_congr
  intro l _
  simp [Bool.and_comm]

private theorem erase_reorder (x : ℕ) (xs : List ℕ) (h : x ∈ xs) (φ : CNF) :
    eraseVariables (x :: xs.erase x) φ = eraseVariables xs φ := by
  unfold eraseVariables
  apply List.map_congr_left
  intro c _
  apply List.filter_congr
  intro l _
  by_cases hl : l.1 = x
  · simp [hl,h]
  · simp [hl]

theorem backdoor_done (k : ℕ) {φ : CNF} (h : IsKCNF 2 φ) : widthTwoBackdoor k φ :=
  ⟨[],Nat.zero_le _,by simpa only [erase_nil]⟩

theorem backdoor_zero (φ : CNF) : widthTwoBackdoor 0 φ ↔ IsKCNF 2 φ := by
  constructor
  · rintro ⟨xs,h,hk⟩
    have hx := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    rwa [hx,erase_nil] at hk
  · exact backdoor_done 0

theorem backdoor_triple (k : ℕ) (l₁ l₂ l₃ : Literal) (r : Clause) (φ : CNF)
    (hc : l₁ :: l₂ :: l₃ :: r ∈ φ) :
    widthTwoBackdoor (k+1) φ ↔
      ∃ x ∈ [l₁.1,l₂.1,l₃.1], widthTwoBackdoor k (eraseVariable x φ) := by
  constructor
  · rintro ⟨xs,hxs,hφ⟩
    have hh : ∃ x ∈ [l₁.1,l₂.1,l₃.1], x ∈ xs := by
      by_contra hn
      have h1 : l₁.1 ∉ xs := fun h => hn ⟨l₁.1,by simp,h⟩
      have h2 : l₂.1 ∉ xs := fun h => hn ⟨l₂.1,by simp,h⟩
      have h3 : l₃.1 ∉ xs := fun h => hn ⟨l₃.1,by simp,h⟩
      let d := (l₁ :: l₂ :: l₃ :: r).filter (fun l => decide (l.1 ∉ xs))
      have hm : d ∈ eraseVariables xs φ := List.mem_map.mpr ⟨_,hc,rfl⟩
      have he := hφ d hm
      simp [d,h1,h2,h3] at he
    obtain ⟨x,hx,hm⟩ := hh
    refine ⟨x,hx,xs.erase x,?_,?_⟩
    · rw [List.length_erase_of_mem hm]
      omega
    · rw [← erase_cons,erase_reorder x xs hm]
      exact hφ
  · rintro ⟨x,_,xs,hxs,hφ⟩
    exact ⟨x :: xs,by simpa using hxs,by rwa [erase_cons]⟩

theorem satisfiable_split (φ : CNF) (x : ℕ) :
    Satisfiable φ ↔ ∃ b : Bool, Satisfiable (restrict x b φ) := by
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨σ x,σ,?_⟩
    simp only [CNF.eval,List.all_eq_true] at hσ ⊢
    intro c hc
    simp only [restrict,List.mem_map,List.mem_filter,decide_eq_true_eq] at hc
    obtain ⟨d,⟨hd,hn⟩,rfl⟩ := hc
    obtain ⟨l,hl,hv⟩ := List.any_eq_true.mp (hσ d hd)
    have he : l.1 ≠ x := by
      intro h
      obtain ⟨i,b⟩ := l
      change i = x at h
      subst i
      have hb : σ x = b := by simpa [Literal.eval] using hv
      exact hn (by simpa [hb] using hl)
    exact List.any_eq_true.mpr ⟨l,List.mem_filter.mpr ⟨hl,by simpa using he⟩,hv⟩
  · rintro ⟨b,σ,hσ⟩
    exact ⟨Function.update σ x b,restrict_eval_update φ x b σ hσ⟩

end PEqualNP.Outside
