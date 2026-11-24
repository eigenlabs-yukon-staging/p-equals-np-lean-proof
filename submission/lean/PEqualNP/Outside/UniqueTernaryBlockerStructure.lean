import PEqualNP.Outside.UniqueZeroClauseBlockers
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Count

namespace PEqualNP.Outside.UniqueTernaryBlocker
open PEqualNP.Search

def blocker (i : ℕ) (c : Clause) : Prop :=
  (i,false) ∈ c ∧ ∀ l ∈ c, l.2 = false → l.1 = i

theorem blocker_inj {i j : ℕ} {c : Clause} (hi : blocker i c) (hj : blocker j c) : i = j :=
  hj.2 (i,false) hi.1 rfl

theorem form (i : ℕ) (c : Clause) (h : blocker i c)
    (hL : c.length = 3) (hN : (c.map Prod.fst).Nodup) :
    ∃ a b : ℕ, i ≠ a ∧ i ≠ b ∧ a ≠ b ∧ c.Perm [(i,false),(a,true),(b,true)] := by
  let rest := c.erase (i,false)
  have hPerm : List.Perm ((i,false)::rest) c := (List.perm_cons_erase h.1).symm
  have hLen : rest.length = 2 := by have hl := hPerm.length_eq; simp at hl; omega
  generalize hEq : rest = rs at hPerm hLen
  rcases rs with _ | ⟨⟨a,p⟩,_ | ⟨⟨b,q⟩,rs⟩⟩
  · cases hLen
  · cases hLen
  · have hRest : rs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hLen; omega)
    subst rs
    have hNd := (hPerm.map Prod.fst).nodup_iff.mpr hN
    have hNe : i ≠ a ∧ i ≠ b ∧ a ≠ b := by simpa [List.nodup_cons,and_assoc] using hNd
    have hP : p = true := by
      cases p
      · have he : a = i := h.2 (a,false) (hPerm.mem_iff.mp (by simp)) rfl
        exact False.elim (hNe.1 he.symm)
      · rfl
    have hQ : q = true := by
      cases q
      · have he : b = i := h.2 (b,false) (hPerm.mem_iff.mp (by simp)) rfl
        exact False.elim (hNe.2.1 he.symm)
      · rfl
    subst p
    subst q
    exact ⟨a,b,hNe.1,hNe.2.1,hNe.2.2,hPerm.symm⟩

theorem all_negative_not_blocker (i : ℕ) (c : Clause)
    (hL : c.length = 3) (hN : (c.map Prod.fst).Nodup) (ha : ∀ l ∈ c, l.2 = false) :
    ¬ blocker i c := by
  intro h
  obtain ⟨a,b,_,_,_,he⟩ := form i c h hL hN
  have hf := ha (a,true) (he.mem_iff.mpr (by simp))
  cases hf

def incidence (F : CNF) (l : Literal) : Finset Clause :=
  F.toFinset.filter (fun c => l ∈ c)

theorem incidence_mem (F : CNF) (l : Literal) (c : Clause) :
    c ∈ incidence F l ↔ c ∈ F ∧ l ∈ c := by simp [incidence]

theorem incidence_le (F : CNF) (l : Literal) : (incidence F l).card ≤ F.flatten.count l := by
  have hEq : incidence F l = (F.filter (fun c => decide (l ∈ c))).toFinset := by
    ext c
    simp [incidence]
  have hLen (F : CNF) : (F.filter (fun c => decide (l ∈ c))).length ≤ F.flatten.count l := by
    induction F with
    | nil => rfl
    | cons c F ih =>
      simp only [List.filter_cons,List.flatten_cons,List.count_append,decide_eq_true_eq]
      by_cases h : l ∈ c
      · simp only [h,ite_true,List.length_cons]
        have hpos := List.count_pos_iff.mpr h
        omega
      · simp only [h,ite_false]
        omega
  rw [hEq]
  exact (List.toFinset_card_le _).trans (hLen F)

theorem signed_count (ls : List Literal) (v : ℕ) :
    (ls.map Prod.fst).count v = ls.count (v,true) + ls.count (v,false) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨i,b⟩ := l
    by_cases hi : i = v
    · subst i
      cases b <;> simp [List.count_cons,ih] <;> omega
    · cases b <;> simp [List.count_cons,hi,Ne.symm hi,ih]

theorem two_negative_cap (F : CNF) (v : ℕ) (c d : Clause)
    (hc : c ∈ F) (hd : d ∈ F) (hNe : c ≠ d)
    (hnc : (v,false) ∈ c) (hnd : (v,false) ∈ d)
    (hD : (F.flatMap (List.map Prod.fst)).count v ≤ 4) : (incidence F (v,true)).card ≤ 2 := by
  have hsub : ({c,d} : Finset Clause) ⊆ incidence F (v,false) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact (incidence_mem ..).mpr ⟨hc,hnc⟩
    · exact (incidence_mem ..).mpr ⟨hd,hnd⟩
  have hNeg : 2 ≤ (incidence F (v,false)).card := by
    simpa [hNe] using Finset.card_le_card hsub
  have h1 := hNeg.trans (incidence_le F (v,false))
  have h2 := incidence_le F (v,true)
  have hEq : F.flatMap (List.map Prod.fst) = F.flatten.map Prod.fst := by
    simp [List.flatMap_def,List.map_flatten]
  rw [hEq,signed_count] at hD
  omega


theorem exists_hole (F : CNF) (T : Finset Clause) (E : Clause) (v : ℕ)
    (hE : E.length = 3 ∧ (E.map Prod.fst).Nodup) (hV : v ∉ E.map Prod.fst)
    (hF : ∀ c ∈ T, c ∈ F)
    (hShape : ∀ c ∈ T, ∃ i a b : ℕ, c.Perm [(i,false),(a,true),(b,true)])
    (hc : (incidence F (v,true)).card ≤ 2) :
    ∃ e ∈ E.map Prod.fst, ∀ c ∈ T, ¬ ((v,true) ∈ c ∧ (e,true) ∈ c) := by
  classical
  let D := (E.map Prod.fst).toFinset
  have hCard : D.card = 3 := by simp [D,List.toFinset_card_of_nodup hE.2,hE.1]
  by_contra h
  push Not at h
  have hPair (e : D) : ∃ c ∈ T, (v,true) ∈ c ∧ (e.1,true) ∈ c := by
    exact h e.1 (List.mem_toFinset.mp e.2)
  choose f hT hPos hTarget using hPair
  have hInj : Function.Injective f := by
    intro a b he
    obtain ⟨i,p,q,hS⟩ := hShape (f a) (hT a)
    have h1 := hS.mem_iff.mp (hPos a)
    have h2 := hS.mem_iff.mp (hTarget a)
    have h3 := hS.mem_iff.mp (he.symm ▸ hTarget b)
    have hVa : v ≠ a.1 := fun h' => hV (h' ▸ List.mem_toFinset.mp a.2)
    have hVb : v ≠ b.1 := fun h' => hV (h' ▸ List.mem_toFinset.mp b.2)
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,Bool.true_eq_false,
      and_false,or_false,and_true] at h1 h2 h3
    apply Subtype.ext
    grind
  let g : D → incidence F (v,true) := fun e =>
    ⟨f e,(incidence_mem ..).mpr ⟨hF _ (hT e),hPos e⟩⟩
  have hg : Function.Injective g := fun a b h => hInj (congrArg Subtype.val h)
  have hle := Fintype.card_le_of_injective g hg
  rw [Fintype.card_coe,Fintype.card_coe,hCard] at hle
  omega

end PEqualNP.Outside.UniqueTernaryBlocker
