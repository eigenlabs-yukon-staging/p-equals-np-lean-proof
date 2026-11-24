import PEqualNP.Outside.ClauseIncidenceHall
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside
open PEqualNP.Search

theorem incidence_count_le (F : CNF) (v : ℕ) :
    ((Finset.univ : Finset (Fin F.length)).filter (fun i => v ∈ clauseVars F i)).card ≤
      (F.flatMap (List.map Prod.fst)).count v := by
  induction F with
  | nil => simp
  | cons c F ih =>
    have hcard := Fin.card_filter_univ_succ' (n := F.length)
      (fun i => v ∈ clauseVars (c::F) i)
    refine Nat.le_trans (Nat.le_of_eq hcard) ?_
    rw [List.flatMap_cons,List.count_append]
    change (if v ∈ clauseVars (c::F) 0 then 1 else 0) +
      ((Finset.univ : Finset (Fin F.length)).filter (fun i => v ∈ clauseVars F i)).card ≤ _
    apply Nat.add_le_add _ ih
    change (if v ∈ (c.map Prod.fst).toFinset then 1 else 0) ≤ _
    split
    · next hv => exact Nat.succ_le_of_lt (List.count_pos_iff.mpr (List.mem_toFinset.mp hv))
    · exact Nat.zero_le _

end PEqualNP.Outside

open PEqualNP.Search

theorem PEqualNP.Outside.StrictTernaryThreeAlwaysSAT :
    ∀ F : CNF,
      (∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup) →
      (∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 3) →
      Satisfiable F := by
  intro F hC hV
  apply PEqualNP.Outside.ClauseIncidenceHall F 3 (by decide)
  · intro i
    obtain ⟨h1,h2⟩ := hC (F.get i) (List.get_mem ..)
    rw [List.toFinset_card_of_nodup h2,List.length_map,h1]
  · intro v
    exact (PEqualNP.Outside.incidence_count_le F v).trans (hV v)
