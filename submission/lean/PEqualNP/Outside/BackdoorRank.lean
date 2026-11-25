import PEqualNP.Outside.TwoSATDeletionBackdoor

namespace PEqualNP.Outside

open PEqualNP.Search PEqualNP.Library.SearchHelpers

def backdoorPick (φ : CNF) : Option (Literal × Literal × Literal) :=
  match (φ.filter (fun c => 2 < c.length)).reverse with
  | (a :: b :: c :: _) :: _ => some (a,b,c)
  | _ => none

theorem backdoor_pick (φ : CNF) :
    (backdoorPick φ = none ↔ IsKCNF 2 φ) ∧
    ∀ a b c, backdoorPick φ = some (a,b,c) → ∃ r, a :: b :: c :: r ∈ φ := by
  have hnone : ((φ.filter (fun c => 2 < c.length)).reverse) = [] ↔ IsKCNF 2 φ := by
    rw [List.reverse_eq_nil_iff,List.filter_eq_nil_iff]
    simp [IsKCNF,decide_eq_true_eq]
  unfold backdoorPick
  cases h : (φ.filter (fun c => 2 < c.length)).reverse with
  | nil =>
      simp only [h] at hnone
      simp [← hnone]
  | cons d ds =>
      have hd := List.mem_filter.mp (List.mem_reverse.mp (h.symm ▸ List.mem_cons_self : d ∈
        (φ.filter (fun c => 2 < c.length)).reverse))
      have hlen : 2 < d.length := of_decide_eq_true hd.2
      obtain _ | ⟨a, _ | ⟨b, _ | ⟨c,r⟩⟩⟩ := d
      · simp at hlen
      · simp at hlen
      · simp at hlen
      · have hb : ¬ IsKCNF 2 φ := by
          intro hφ
          have := hφ _ hd.1
          omega
        refine ⟨by simp [hb],?_⟩
        intro x y z he
        cases he
        exact ⟨r,hd.1⟩

def rankedKey (l₁ l₂ l₃ : Literal) (d : ℕ) : ℕ :=
  if d % 3 = 0 then l₁.1 else if d % 3 = 1 then l₂.1 else l₃.1

def rankedPolarity (d : ℕ) : Bool := decide (d < 3)

private theorem ranked_key_mem (l₁ l₂ l₃ : Literal) (d : ℕ) :
    rankedKey l₁ l₂ l₃ d ∈ [l₁.1,l₂.1,l₃.1] := by
  unfold rankedKey
  by_cases h : d % 3 = 0
  · simp [h]
  · by_cases h' : d % 3 = 1 <;> simp [h,h']

private theorem ranked_digit (l₁ l₂ l₃ : Literal) (x : ℕ) (b : Bool)
    (h : x ∈ [l₁.1,l₂.1,l₃.1]) :
    ∃ d < 6, rankedKey l₁ l₂ l₃ d = x ∧ rankedPolarity d = b := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl <;> cases b
  · exact ⟨3,by decide,rfl,rfl⟩
  · exact ⟨0,by decide,rfl,rfl⟩
  · exact ⟨4,by decide,rfl,rfl⟩
  · exact ⟨1,by decide,rfl,rfl⟩
  · exact ⟨5,by decide,rfl,rfl⟩
  · exact ⟨2,by decide,rfl,rfl⟩

def rankedWalk : ℕ → ℕ → ℕ → CNF → CNF → Prop
  | 0, _, _, φ, ψ => IsKCNF 2 φ ∧ Satisfiable ψ
  | n+1, B, j, φ, ψ =>
      match backdoorPick φ with
      | none => Satisfiable ψ
      | some (a,b,c) =>
          6 ≤ B ∧
            let d := j % 6
            let x := rankedKey a b c d
            rankedWalk n (B/6) (j/6) (eraseVariable x φ) (restrict x (rankedPolarity d) ψ)

theorem ranked_sound (n B j : ℕ) (hB : 1 ≤ B) (φ ψ : CNF)
    (h : rankedWalk n B j φ ψ) :
    (∃ k : ℕ, 6^k ≤ B ∧ widthTwoBackdoor k φ) ∧ Satisfiable ψ := by
  induction n generalizing B j φ ψ with
  | zero =>
      exact ⟨⟨0,hB,backdoor_done 0 h.1⟩,h.2⟩
  | succ n ih =>
      cases hp : backdoorPick φ with
      | none =>
          rw [rankedWalk,hp] at h
          exact ⟨⟨0,hB,backdoor_done 0 ((backdoor_pick φ).1.mp hp)⟩,h⟩
      | some item =>
          obtain ⟨l₁,l₂,l₃⟩ := item
          obtain ⟨r,hr⟩ := (backdoor_pick φ).2 l₁ l₂ l₃ hp
          rw [rankedWalk,hp] at h
          obtain ⟨hb,hw⟩ := h
          let d := j % 6
          let x := rankedKey l₁ l₂ l₃ d
          have hz : 1 ≤ B/6 := by omega
          obtain ⟨⟨k,hk,hs⟩,hsat⟩ := ih (B/6) (j/6) hz _ _ hw
          refine ⟨⟨k+1,?_,(backdoor_triple k l₁ l₂ l₃ r φ hr).mpr
            ⟨x,ranked_key_mem l₁ l₂ l₃ d,hs⟩⟩,(satisfiable_split ψ x).mpr ⟨rankedPolarity d,hsat⟩⟩
          rw [pow_succ]
          omega

theorem ranked_complete (n B k : ℕ) (hf : B ≤ n) (hk : 6^k ≤ B)
    (φ ψ : CNF) (hback : widthTwoBackdoor k φ) (hs : Satisfiable ψ) :
    ∃ j < B, rankedWalk n B j φ ψ := by
  have hB : 0 < B := lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 6)) hk
  induction n generalizing B k φ ψ with
  | zero => omega
  | succ n ih =>
      cases hp : backdoorPick φ with
      | none => exact ⟨0,hB,by rw [rankedWalk,hp]; exact hs⟩
      | some item =>
          obtain ⟨l₁,l₂,l₃⟩ := item
          obtain ⟨r,hr⟩ := (backdoor_pick φ).2 l₁ l₂ l₃ hp
          cases k with
          | zero =>
              have hφ := (backdoor_zero φ).mp hback
              rw [(backdoor_pick φ).1.mpr hφ] at hp
              contradiction
          | succ k =>
              obtain ⟨x,hx,hback'⟩ := (backdoor_triple k l₁ l₂ l₃ r φ hr).mp hback
              obtain ⟨b,hs'⟩ := (satisfiable_split ψ x).mp hs
              obtain ⟨d,hd,he,he'⟩ := ranked_digit l₁ l₂ l₃ x b hx
              rw [pow_succ] at hk
              have hpos : 0 < 6^k := Nat.pow_pos (by decide)
              have hB' : 6 ≤ B := by omega
              have hf' : B/6 ≤ n := by omega
              have hk' : 6^k ≤ B/6 := by omega
              obtain ⟨j,hj,hw⟩ := ih (B/6) k hf' hk' _ _ hback' hs' (by omega)
              have hmod : (6*j+d)%6 = d := by omega
              have hdiv : (6*j+d)/6 = j := by omega
              refine ⟨6*j+d,by omega,?_⟩
              rw [rankedWalk,hp]
              dsimp only
              rw [hdiv,hmod,he,he']
              exact ⟨hB',hw⟩

end PEqualNP.Outside
