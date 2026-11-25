import PEqualNP.Outside.LocalityEliminationWidth
import Mathlib.Data.List.Basic

namespace PEqualNP.Outside

private theorem rank_width (rank : ℕ → ℕ) (k : ℕ) (c : NatClause)
    (hinj : ∀ p ∈ c, ∀ q ∈ c, rank p.1 = rank q.1 → p.1 = q.1)
    (hl : ∀ p ∈ c, ∀ q ∈ c, rank p.1 ≤ rank q.1 + k) : c.card ≤ 2 * (k+1) := by
  let mapLit := fun p : ℕ × Bool => (rank p.1,p.2)
  have hi : Set.InjOn mapLit ↑c := by
    intro p hp q hq he
    have hr := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    exact Prod.ext (hinj p hp q hq hr) hs
  rw [← Finset.card_image_of_injOn hi]
  apply signed_locality_width k
  intro p hp q hq
  obtain ⟨l,hl',rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hq
  exact hl l hl' m hm

theorem elimination_survivors (F : Set NatClause) (order : List ℕ) :
    ∀ c ∈ order.foldl (fun G x => eliminateVariable x G) F,
      ∀ l ∈ c, (∃ d ∈ F, l ∈ d) ∧ l.1 ∉ order := by
  induction order generalizing F with
  | nil => exact fun c hc l hl => ⟨⟨c,hc,hl⟩,List.not_mem_nil⟩
  | cons x xs ih =>
    intro c hc l hl
    obtain ⟨⟨d,hd,hld⟩,hnot⟩ := ih (eliminateVariable x F) c hc l hl
    obtain ⟨hne,e,he,hle⟩ := eliminate_support hd l hld
    exact ⟨⟨e,he,hle⟩,fun h => (List.mem_cons.mp h).elim hne hnot⟩

private theorem occurrence_minimum (order : List ℕ) (j : ℕ) (hj : j < order.length)
    (v : ℕ) (hv : v ∈ order) (hNot : v ∉ order.take j) : order.idxOf order[j] ≤ order.idxOf v := by
  have hx : order[j] ∈ order.take (j+1) := by
    exact (List.take_succ_eq_append_getElem hj).symm ▸ List.mem_append_right _ (List.mem_singleton_self _)
  have hj' : order.idxOf order[j] < j+1 := (List.mem_take_iff_idxOf_lt (List.getElem_mem hj)).mp hx
  have hv' : j ≤ order.idxOf v := Nat.le_of_not_gt (fun h => hNot ((List.mem_take_iff_idxOf_lt hv).mpr h))
  omega

theorem first_occurrence_stage_locality (k : ℕ) (F : Set NatClause) (order : List ℕ)
    (hLocal : eliminationLocality (fun x => order.idxOf x) k F)
    (hSupport : ∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order) :
    ∀ j ≤ order.length, eliminationLocality (fun x => order.idxOf x) k
      ((order.take j).foldl (fun G x => eliminateVariable x G) F) := by
  let rank := fun x => order.idxOf x
  let stage := fun j : ℕ => (order.take j).foldl (fun G x => eliminateVariable x G) F
  change ∀ j ≤ order.length, eliminationLocality rank k (stage j)
  intro j
  induction j with
  | zero => exact fun _ => hLocal
  | succ j ih =>
    intro hj
    have hlt := Nat.lt_of_succ_le hj
    have hstage : stage (j+1) = eliminateVariable order[j] (stage j) := by
      simp only [stage,List.take_succ_eq_append_getElem hlt,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [hstage]
    apply eliminationLocality_step rank k _ _ (ih hlt.le)
    intro c hc l hl
    obtain ⟨⟨d,hd,hld⟩,hNot⟩ := elimination_survivors F (order.take j) c hc l hl
    exact occurrence_minimum order j hlt l.1 (hSupport d hd l hld) hNot

/-- Using first-occurrence ranks as coordinates, scanning an order with
repetitions preserves bounded distances among co-occurring variables. -/
theorem FirstOccurrenceEliminationWidth (k : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause ℕ)) (order : List ℕ) :
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    (∀ c ∈ F, ∀ p ∈ c, ∀ q ∈ c, order.idxOf p.1 ≤ order.idxOf q.1 + k) →
    (∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order) →
    ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl eliminate F, Finset.card c ≤ 2 * (k+1) := by
  dsimp only
  intro hLocal hSupport
  let rank := fun x => order.idxOf x
  let stage := fun j : ℕ => (order.take j).foldl (fun G x => eliminateVariable x G) F
  have hStageLocal := first_occurrence_stage_locality k F order hLocal hSupport
  intro j hj c hc
  change c ∈ stage j at hc
  apply rank_width rank k c _ (hStageLocal j hj c hc)
  intro p hp q hq he
  obtain ⟨⟨d,hd,hpd⟩,_⟩ := elimination_survivors F (order.take j) c hc p hp
  exact (List.idxOf_inj (hSupport d hd p hpd)).mp he

end PEqualNP.Outside
