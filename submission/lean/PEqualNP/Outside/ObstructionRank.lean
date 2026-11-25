import PEqualNP.Outside.VariableDeletionCorrect

namespace PEqualNP.Outside

open PEqualNP.Search PEqualNP.Library.SearchHelpers

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

private theorem add_key (A : CNF → Prop) (φ : CNF) (x k : ℕ)
    (h : hasDeletionSet A k (eraseVariable x φ)) :
    hasDeletionSet A (k+1) φ := by
  obtain ⟨xs,hxs,hA⟩ := h
  exact ⟨x :: xs,by simpa using hxs,by rwa [erase_cons]⟩

private theorem remove_key (A : CNF → Prop) (φ : CNF) (xs : List ℕ) (x k : ℕ)
    (h : x ∈ xs) (hlen : xs.length ≤ k+1) (hA : A (eraseVariables xs φ)) :
    hasDeletionSet A k (eraseVariable x φ) := by
  refine ⟨xs.erase x,?_,?_⟩
  · rw [List.length_erase_of_mem h]
    omega
  · rw [← erase_cons,erase_reorder x xs h]
    exact hA

def chooseRankKey (xs : List ℕ) (i : ℕ) : ℕ := (xs[i]?).getD (xs.headD 0)

theorem rank_key_mem (xs : List ℕ) (i : ℕ) (h : xs ≠ []) : chooseRankKey xs i ∈ xs := by
  unfold chooseRankKey
  by_cases hl : i < xs.length
  · rw [List.getElem?_eq_getElem hl]
    exact List.getElem_mem hl
  · have hh : xs.length ≤ i := by omega
    rw [List.getElem?_eq_none hh]
    cases xs with
    | nil => contradiction
    | cons x xs => exact List.mem_cons_self

theorem rank_key_digit (a : ℕ) (xs : List ℕ) (x : ℕ) (b : Bool)
    (hx : x ∈ xs) (ha : xs.length ≤ a) :
    ∃ d < 2*a, chooseRankKey xs (d % a) = x ∧ decide (d < a) = b := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  have hia : i < a := hi.trans_le ha
  have hs : chooseRankKey xs i = x := by
    unfold chooseRankKey
    rw [List.getElem?_eq_getElem hi]
    exact he
  cases b
  · refine ⟨a+i,by omega,?_,by simp⟩
    rw [Nat.add_comm a i,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod, Nat.mod_eq_of_lt hia]
    exact hs
  · exact ⟨i,by omega,by simpa [Nat.mod_eq_of_lt hia] using hs,by simp [hia]⟩

/-- One rank-selected path of the bounded-obstruction variable-deletion tree. -/
def obstructionWalk (A : CNF → Prop) (select : CNF → List ℕ) (a : ℕ) :
    ℕ → ℕ → ℕ → CNF → CNF → Prop
  | 0, _, _, φ, ψ => A φ ∧ Satisfiable ψ
  | n+1, B, j, φ, ψ =>
      if select φ = [] then Satisfiable ψ else
        2*a ≤ B ∧
          let d := j % (2*a)
          let x := chooseRankKey (select φ) (d%a)
          obstructionWalk A select a n (B/(2*a)) (j/(2*a))
            (eraseVariable x φ) (restrict x (decide (d < a)) ψ)

theorem obstruction_sound (A : CNF → Prop) (select : CNF → List ℕ) (a : ℕ) (ha : 0 < a)
    (hclear : ∀ φ, select φ = [] ↔ A φ) (n B j : ℕ) (hB : 1 ≤ B) (φ ψ : CNF)
    (h : obstructionWalk A select a n B j φ ψ) :
    (∃ k : ℕ, (2*a)^k ≤ B ∧ hasDeletionSet A k φ) ∧ Satisfiable ψ := by
  induction n generalizing B j φ ψ with
  | zero => exact ⟨⟨0,hB,(hasDeletionSet_zero A φ).mpr h.1⟩,h.2⟩
  | succ n ih =>
      by_cases hs : select φ = []
      · simp only [obstructionWalk,hs,ite_true] at h
        exact ⟨⟨0,hB,(hasDeletionSet_zero A φ).mpr ((hclear φ).mp hs)⟩,h⟩
      · simp only [obstructionWalk,hs,ite_false] at h
        obtain ⟨hb,hw⟩ := h
        have ha' : 0 < 2*a := by omega
        have hz : 1 ≤ B/(2*a) := Nat.div_pos hb ha'
        obtain ⟨⟨k,hk,hdel⟩,hSat⟩ := ih (B/(2*a)) (j/(2*a)) hz _ _ hw
        refine ⟨⟨k+1,?_,add_key A φ _ k hdel⟩,(satisfiable_split ψ _).mpr ⟨_,hSat⟩⟩
        rw [pow_succ]
        exact (Nat.mul_le_mul_right (2*a) hk).trans (Nat.div_mul_le_self _ _)

theorem obstruction_complete (A : CNF → Prop) (select : CNF → List ℕ) (a : ℕ) (ha : 0 < a)
    (hclear : ∀ φ, select φ = [] ↔ A φ)
    (hhit : ∀ φ xs, A (eraseVariables xs φ) → select φ ≠ [] → ∃ x ∈ select φ, x ∈ xs)
    (hlen : ∀ φ, (select φ).length ≤ a) (n B k : ℕ) (hf : B ≤ n) (hk : (2*a)^k ≤ B)
    (φ ψ : CNF) (hdel : hasDeletionSet A k φ) (hSat : Satisfiable ψ) :
    ∃ j < B, obstructionWalk A select a n B j φ ψ := by
  have ha' : 0 < 2*a := by omega
  have hB : 0 < B := lt_of_lt_of_le (Nat.pow_pos ha') hk
  induction n generalizing B k φ ψ with
  | zero => omega
  | succ n ih =>
      by_cases hz : select φ = []
      · exact ⟨0,hB,by simpa only [obstructionWalk,hz,ite_true] using hSat⟩
      · cases k with
        | zero => exact (hz ((hclear φ).mpr ((hasDeletionSet_zero A φ).mp hdel))).elim
        | succ k =>
            obtain ⟨xs,hxs,hA⟩ := hdel
            obtain ⟨x,hx,hxs'⟩ := hhit φ xs hA hz
            have hdel' := remove_key A φ xs x k hxs' hxs hA
            obtain ⟨b,hSat'⟩ := (satisfiable_split ψ x).mp hSat
            obtain ⟨d,hd,hkey,hb⟩ := rank_key_digit a (select φ) x b hx (hlen φ)
            rw [pow_succ] at hk
            have hpow : 0 < (2*a)^k := Nat.pow_pos ha'
            have hlim : 2*a ≤ B := (Nat.le_mul_of_pos_left _ hpow).trans hk
            have hquot : B/(2*a) ≤ n := by
              have hlt := Nat.div_lt_self hB (show 1 < 2*a by omega)
              omega
            have hk' : (2*a)^k ≤ B/(2*a) := (Nat.le_div_iff_mul_le ha').mpr hk
            have hpos : 0 < B/(2*a) := Nat.div_pos hlim ha'
            obtain ⟨j,hj,hw⟩ := ih (B/(2*a)) k hquot hk' _ _ hdel' hSat' hpos
            have hm : (2*a)*j+d < B := by
              calc
                (2*a)*j+d < (2*a)*j+(2*a) := Nat.add_lt_add_left hd _
                _ = (2*a)*(j+1) := (Nat.mul_succ _ _).symm
                _ ≤ (2*a)*(B/(2*a)) := Nat.mul_le_mul_left _ hj
                _ ≤ B := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self B (2*a)
            have hmod : ((2*a)*j+d)%(2*a) = d := by
              rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hd]
            refine ⟨(2*a)*j+d,hm,?_⟩
            simp only [obstructionWalk,hz,ite_false, hlim,true_and,
              hmod,Nat.mul_add_div ha',Nat.div_eq_of_lt hd,Nat.add_zero,hkey,hb]
            exact hw

end PEqualNP.Outside
