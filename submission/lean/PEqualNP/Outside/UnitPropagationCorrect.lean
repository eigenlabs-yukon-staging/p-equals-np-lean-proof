import PEqualNP.Defs.SearchRUP
import PEqualNP.Defs.Search
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside

open PEqualNP.Search

abbrev FinClause := PEqualNP.ProofComplexity.Clause ℕ

def clauseSet (φ : CNF) : Set FinClause := {c | ∃ d ∈ φ, d.toFinset = c}

def canForce (known : List Literal) (c : Clause) (l : Literal) : Bool :=
  c.all (fun m => decide (m = l) || decide (negLit m ∈ known))

theorem canForce_spec (known : List Literal) (c : Clause) (l : Literal) :
    canForce known c l = true ↔ ∀ m ∈ c, m ≠ l → negLit m ∈ known := by
  simp only [canForce,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro h m hm hne
    exact (h m hm).resolve_left hne
  · intro h m hm
    by_cases he : m = l
    · exact Or.inl he
    · exact Or.inr (h m hm he)

def unitRound (φ : CNF) (assumed known : List Literal) : List Literal :=
  assumed ++ φ.flatMap (fun c => c.filter (canForce known c))

def unitKnown (φ : CNF) (assumed : List Literal) : ℕ → List Literal
  | 0 => assumed
  | n+1 => unitRound φ assumed (unitKnown φ assumed n)

theorem round_mono (φ : CNF) (A : List Literal) {L M : List Literal} (h : L ⊆ M) :
    unitRound φ A L ⊆ unitRound φ A M := by
  intro x hx
  simp only [unitRound,List.mem_append,List.mem_flatMap,List.mem_filter] at hx ⊢
  rcases hx with hA | ⟨c,hc,hx,hgood⟩
  · exact Or.inl hA
  · apply Or.inr
    refine ⟨c,hc,hx,(canForce_spec M c x).mpr (fun t ht ht' => ?_)⟩
    exact h ((canForce_spec L c x).mp hgood t ht ht')

theorem unit_step_mono (φ : CNF) (A : List Literal) (n : ℕ) :
    unitKnown φ A n ⊆ unitKnown φ A (n+1) := by
  induction n with
  | zero => exact fun _ h => List.mem_append_left _ h
  | succ n ih => exact round_mono φ A ih

private theorem local_sublist (φ : CNF) (L : List Literal) :
    (φ.flatMap (fun c => c.filter (canForce L c))).Sublist (φ.flatMap id) := by
  induction φ with
  | nil => exact .slnil
  | cons c φ ih =>
      simp only [List.flatMap_cons,id_eq]
      exact List.Sublist.append List.filter_sublist ih

theorem unit_sublist (φ : CNF) (A : List Literal) (n : ℕ) :
    (unitKnown φ A n).Sublist (A ++ φ.flatMap id) := by
  cases n with
  | zero => exact List.sublist_append_left _ _
  | succ n => exact List.Sublist.append (List.Sublist.refl _) (local_sublist φ _)

private theorem to_set_mono {L M : List Literal} (h : L ⊆ M) : L.toFinset ⊆ M.toFinset :=
  fun _ hx => List.mem_toFinset.mpr (h (List.mem_toFinset.mp hx))

private theorem to_list_mono {L M : List Literal} (h : L.toFinset ⊆ M.toFinset) : L ⊆ M :=
  fun _ hx => List.mem_toFinset.mp (h (List.mem_toFinset.mpr hx))

private theorem round_stable_next (φ : CNF) (A : List Literal) (n : ℕ)
    (h : (unitKnown φ A n).toFinset = (unitKnown φ A (n+1)).toFinset) :
    (unitKnown φ A (n+1)).toFinset = (unitKnown φ A (n+2)).toFinset := by
  apply Finset.Subset.antisymm
  · exact to_set_mono (unit_step_mono φ A (n+1))
  · exact to_set_mono (round_mono φ A (to_list_mono (le_of_eq h.symm)))

private theorem card_progress (φ : CNF) (A : List Literal) (n : ℕ)
    (h : (unitKnown φ A n).toFinset ≠ (unitKnown φ A (n+1)).toFinset) :
    n+1 ≤ (unitKnown φ A (n+1)).toFinset.card := by
  have hlt : (unitKnown φ A n).toFinset.card < (unitKnown φ A (n+1)).toFinset.card :=
    Finset.card_lt_card (lt_of_le_of_ne (to_set_mono (unit_step_mono φ A n)) h)
  induction n with
  | zero => omega
  | succ n ih =>
      have hne : (unitKnown φ A n).toFinset ≠ (unitKnown φ A (n+1)).toFinset :=
        fun he => h (round_stable_next φ A n he)
      have ht : (unitKnown φ A n).toFinset.card < (unitKnown φ A (n+1)).toFinset.card :=
        Finset.card_lt_card (lt_of_le_of_ne (to_set_mono (unit_step_mono φ A n)) hne)
      have := ih hne ht
      omega

private theorem closure_stable (φ : CNF) (A : List Literal) (n : ℕ)
    (hn : (A ++ φ.flatMap id).length ≤ n) :
    (unitKnown φ A n).toFinset = (unitKnown φ A (n+1)).toFinset := by
  by_contra h
  have hcard := card_progress φ A n h
  have hs := Finset.card_le_card (to_set_mono (unit_sublist φ A (n+1)).subset)
  have hb := List.toFinset_card_le (l := A ++ φ.flatMap id)
  omega

theorem unit_sound (φ : CNF) (A : List Literal) (n : ℕ) {l : Literal}
    (h : l ∈ unitKnown φ A n) :
    UPForces (clauseSet φ) {x | x ∈ A} l := by
  induction n generalizing l with
  | zero => exact .hyp h
  | succ n ih =>
      change l ∈ unitRound φ A (unitKnown φ A n) at h
      simp only [unitRound,List.mem_append,List.mem_flatMap,List.mem_filter] at h
      rcases h with ha | ⟨c,hc,hl,hforce⟩
      · exact .hyp ha
      · refine .unit (D := c.toFinset) ⟨c,hc,rfl⟩ (List.mem_toFinset.mpr hl) ?_
        intro m hm hne
        exact ih ((canForce_spec _ _ _).mp hforce m (List.mem_toFinset.mp hm) hne)

theorem unit_complete (φ : CNF) (A : List Literal) (n : ℕ)
    (hn : (A ++ φ.flatMap id).length ≤ n) {l : Literal}
    (h : UPForces (clauseSet φ) {x | x ∈ A} l) : l ∈ unitKnown φ A n := by
  have hs := to_list_mono (le_of_eq (closure_stable φ A n hn).symm)
  induction h with
  | @hyp l h => exact hs (List.mem_append_left _ h)
  | @unit C l hC hl _ ih =>
      obtain ⟨c,hc,rfl⟩ := hC
      apply hs
      change l ∈ unitRound φ A (unitKnown φ A n)
      apply List.mem_append_right
      refine List.mem_flatMap.mpr ⟨c,hc,List.mem_filter.mpr ⟨List.mem_toFinset.mp hl,?_⟩⟩
      exact (canForce_spec _ _ _).mpr (fun m hm hne => ih m (List.mem_toFinset.mpr hm) hne)

def falsified (φ : CNF) (known : List Literal) : Bool :=
  φ.any (fun c => c.all (fun l => decide (negLit l ∈ known)))

theorem rup_iff (φ : CNF) (c : Clause) (n : ℕ)
    (hn : ((c.map negLit) ++ φ.flatMap id).length ≤ n) :
    falsified φ (unitKnown φ (c.map negLit) n) = true ↔ IsRUP (clauseSet φ) c.toFinset := by
  have hA : {x | x ∈ c.map negLit} = negLit '' (↑c.toFinset : Set Literal) := by
    ext l
    simp only [Set.mem_setOf_eq,List.mem_map,Set.mem_image,Finset.mem_coe,List.mem_toFinset]
  simp only [falsified,List.any_eq_true,List.all_eq_true,decide_eq_true_eq,IsRUP]
  constructor
  · rintro ⟨d,hd,h⟩
    refine ⟨d.toFinset,⟨d,hd,rfl⟩,fun l hl => ?_⟩
    rw [← hA]
    exact unit_sound φ _ n (h l (List.mem_toFinset.mp hl))
  · rintro ⟨d,⟨e,he,rfl⟩,h⟩
    refine ⟨e,he,fun l hl => ?_⟩
    apply unit_complete φ _ n hn
    rw [hA]
    exact h l (List.mem_toFinset.mpr hl)

end PEqualNP.Outside
