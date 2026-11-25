import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate

namespace PEqualNP.Outside

/-- Iteration of a monotone list rule from the empty list reaches extensional
stability once the clock reaches the length of a fixed ambient list. -/
theorem FiniteListFixedPoint {α : Type} (f : List α → List α) (ambient : List α)
    (hmono : ∀ L M, L ⊆ M → f L ⊆ f M)
    (hbound : ∀ L, f L ⊆ ambient) (n : ℕ) (hn : ambient.length ≤ n) :
    ∀ x, x ∈ f^[n] ([] : List α) ↔ x ∈ f (f^[n] []) := by
  classical
  let run := fun i : ℕ => f^[i] ([] : List α)
  have step (i : ℕ) : run (i+1) = f (run i) := Function.iterate_succ_apply' f i []
  have grow (i : ℕ) : run i ⊆ run (i+1) := by
    induction i with
    | zero => simp [run]
    | succ i ih =>
        rw [step (i+1)]
        have h := hmono _ _ ih
        rwa [← step i] at h
  have setMono {L M : List α} (h : L ⊆ M) : L.toFinset ⊆ M.toFinset :=
    fun _ hx => List.mem_toFinset.mpr (h (List.mem_toFinset.mp hx))
  have listMono {L M : List α} (h : L.toFinset ⊆ M.toFinset) : L ⊆ M :=
    fun _ hx => List.mem_toFinset.mp (h (List.mem_toFinset.mpr hx))
  have stable (i : ℕ) (h : (run i).toFinset = (run (i+1)).toFinset) :
      (run (i+1)).toFinset = (run (i+2)).toFinset := by
    apply Finset.Subset.antisymm (setMono (grow (i+1)))
    rw [step (i+1)]
    have hsub : run (i+1) ⊆ run i := listMono (le_of_eq h.symm)
    have hw := hmono _ _ hsub
    rw [← step i] at hw
    exact setMono hw
  have strict (i : ℕ) (h : (run i).toFinset ≠ (run (i+1)).toFinset) :
      (run i).toFinset.card < (run (i+1)).toFinset.card :=
    Finset.card_lt_card (lt_of_le_of_ne (setMono (grow i)) h)
  have progress (i : ℕ) (h : (run i).toFinset ≠ (run (i+1)).toFinset) :
      i+1 ≤ (run (i+1)).toFinset.card := by
    induction i with
    | zero =>
        have h' := strict 0 h
        omega
    | succ i ih =>
        have h' := ih (fun e => h (stable i e))
        have he := strict (i+1) h
        omega
  have done : (run n).toFinset = (run (n+1)).toFinset := by
    by_contra h
    have h' := progress n h
    have hu : run (n+1) ⊆ ambient := by rw [step n]; exact hbound _
    have hcard := Finset.card_le_card (setMono hu)
    have hlen := List.toFinset_card_le (l := ambient)
    omega
  intro x
  change x ∈ run n ↔ x ∈ f (run n)
  rw [← step n,← List.mem_toFinset,done,List.mem_toFinset]

end PEqualNP.Outside
