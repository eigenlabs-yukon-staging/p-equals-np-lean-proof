import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Finite

namespace PEqualNP.Outside
open PEqualNP.Search

def clauseVars (F : CNF) (i : Fin F.length) : Finset ℕ :=
  ((F.get i).map Prod.fst).toFinset

theorem incidence_hall {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Finset ℕ) (d : ℕ)
    (hd : 0 < d) (hdegree : ∀ i, d ≤ (N i).card)
    (hcap : ∀ v, ((Finset.univ : Finset ι).filter (fun i => v ∈ N i)).card ≤ d) :
    ∀ S : Finset ι, S.card ≤ (S.biUnion N).card := by
  intro S
  let U := S.biUnion N
  have hL : S.card*d ≤ ∑ i ∈ S, (N i).card := by
    simpa using Finset.sum_le_sum (s := S) (fun i _ => hdegree i)
  have hmid : (∑ i ∈ S, (N i).card) =
      ∑ v ∈ U, ((S.filter fun i => v ∈ N i).card) := by
    calc
      _ = ∑ i ∈ S, ∑ v ∈ U, if v ∈ N i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_filter]
        have he : U.filter (fun v => v ∈ N i) = N i := by
          apply Finset.ext
          simp only [Finset.mem_filter]
          exact fun v => ⟨And.right,fun hv => ⟨Finset.mem_biUnion.mpr ⟨i,hi,hv⟩,hv⟩⟩
        simp [he]
      _ = ∑ v ∈ U, ∑ i ∈ S, if v ∈ N i then 1 else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← Finset.sum_filter]
        simp
  have hR : (∑ v ∈ U, (S.filter fun i => v ∈ N i).card) ≤ U.card*d := by
    have hs : ∀ v, (S.filter fun i => v ∈ N i).card ≤ d := by
      intro v
      apply (Finset.card_le_card ?_).trans (hcap v)
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    simpa using Finset.sum_le_sum (s := U) (fun v _ => hs v)
  rw [hmid] at hL
  exact Nat.le_of_mul_le_mul_right (hL.trans hR) hd

theorem matching_satisfies (F : CNF) (m : Fin F.length → ℕ)
    (hm : Function.Injective m) (h : ∀ i, m i ∈ clauseVars F i) : Satisfiable F := by
  classical
  have hpol : ∀ i, ∃ b : Bool, (m i,b) ∈ F.get i := by
    intro i
    have hh : m i ∈ (F.get i).map Prod.fst := List.mem_toFinset.mp (h i)
    obtain ⟨⟨v,b⟩,hv,rfl⟩ := List.mem_map.mp hh
    exact ⟨b,hv⟩
  choose pol hp using hpol
  let σ : Assignment := fun v =>
    if h : ∃ i, m i = v then pol (Classical.choose h) else false
  have hσ (i : Fin F.length) : σ (m i) = pol i := by
    have hex : ∃ j, m j = m i := ⟨i,rfl⟩
    unfold σ
    rw [dite_eq_left hex,hm (Classical.choose_spec hex)]
  refine ⟨σ,?_⟩
  simp only [CNF.eval,List.all_eq_true]
  intro cl hc
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
  apply List.any_eq_true.mpr
  let j : Fin F.length := ⟨i,hi⟩
  exact ⟨(m j,pol j),hp j,by simp [Literal.eval,hσ j]⟩

end PEqualNP.Outside

open PEqualNP.Search

theorem PEqualNP.Outside.ClauseIncidenceHall :
    ∀ (F : CNF) (d : ℕ), 0 < d →
      (∀ i : Fin F.length, d ≤ ((F.get i).map Prod.fst).toFinset.card) →
      (∀ v : ℕ,
        ((Finset.univ : Finset (Fin F.length)).filter
          (fun i => v ∈ ((F.get i).map Prod.fst).toFinset)).card ≤ d) →
      Satisfiable F := by
  intro F d hd hC hV
  open PEqualNP.Outside in
  obtain ⟨m,hm,h⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' (clauseVars F)).mp
    (incidence_hall (clauseVars F) d hd hC hV)
  exact PEqualNP.Outside.matching_satisfies F m hm h
