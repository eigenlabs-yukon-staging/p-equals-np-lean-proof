import PEqualNP.Outside.FirstOccurrenceEliminationWidth
import PEqualNP.Outside.UnitPropagationCorrect

namespace PEqualNP.Outside

open PEqualNP.Search

private def window (k : ℕ) (c : Clause) (i : ℕ) : Clause :=
  ((c.drop i).take (k+1)).flatMap (fun l => [l,(l.1,!l.2)])

private theorem at_rank_in_window (k i : ℕ) (c : Clause) (l : Literal)
    (hOcc : l.1 ∈ c.map Prod.fst)
    (hLo : i ≤ (c.map Prod.fst).idxOf l.1)
    (hHi : (c.map Prod.fst).idxOf l.1 ≤ i+k) : l ∈ window k c i := by
  let r := (c.map Prod.fst).idxOf l.1
  have hr : r < c.length := by simpa [r] using List.idxOf_lt_length_of_mem hOcc
  have hVar : c[r].1 = l.1 := by
    have hm : r < (c.map Prod.fst).length := by simpa using hr
    have he : (c.map Prod.fst)[r]'hm = l.1 := List.getElem_idxOf hm
    simpa only [List.getElem_map] using he
  let j := r-i
  have hj : j < ((c.drop i).take (k+1)).length := by
    rw [List.length_take,List.length_drop,Nat.lt_min]
    dsimp only [j]
    change i ≤ r at hLo
    change r ≤ i+k at hHi
    omega
  have hList : c[r] ∈ (c.drop i).take (k+1) := by
    have hv := List.getElem_mem hj
    rw [List.getElem_take,List.getElem_drop] at hv
    have he : i+j = r := Nat.add_sub_of_le hLo
    simpa only [he] using hv
  rw [window,List.mem_flatMap]
  refine ⟨c[r],hList,?_⟩
  rcases hl : l.2 <;> rcases hc : c[r].2 <;> simp [Prod.ext_iff,hVar,hl,hc]

/-- A catalogue of signed occurrence windows contains a representative of
every stage clause for a formula with bounded first-occurrence radius. -/
theorem LocalityUniverseCoverage (k : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause ℕ)) (c : Clause) (U : CNF) :
    let order := c.map Prod.fst
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    (∀ d : Clause, d ∈ U ↔ d = [] ∨ ∃ i < c.length,
      d.Sublist (((c.drop i).take (k+1)).flatMap (fun l => [l,(l.1,!l.2)]))) →
    (∀ d ∈ F, ∀ l ∈ d, ∀ m ∈ d, order.idxOf l.1 ≤ order.idxOf m.1 + k) →
    (∀ d ∈ F, ∀ l ∈ d, l.1 ∈ order) →
    ∀ j ≤ order.length, (order.take j).foldl eliminate F ⊆
      {D : PEqualNP.ProofComplexity.Clause ℕ | ∃ d ∈ U, d.toFinset = D} := by
  dsimp only
  intro hU hLoc hSupp j hj d hd
  change d ∈ ((c.map Prod.fst).take j).foldl (fun G x => eliminateVariable x G) F at hd
  by_cases hz : d.Nonempty
  · let order := c.map Prod.fst
    let ranks := d.image (fun l => order.idxOf l.1)
    have hRanks : ranks.Nonempty := hz.image _
    let i := ranks.min' hRanks
    obtain ⟨pivot,hPivot,hRank⟩ := Finset.mem_image.mp (Finset.min'_mem ranks hRanks)
    change order.idxOf pivot.1 = i at hRank
    have hSup (l : Literal) (hl : l ∈ d) : l.1 ∈ order := by
      obtain ⟨⟨e,he,hLit⟩,_⟩ := elimination_survivors F (order.take j) d hd l hl
      exact hSupp e he l hLit
    have hi : i < c.length := by
      rw [← hRank]
      simpa [order] using List.idxOf_lt_length_of_mem (hSup pivot hPivot)
    have hLocal := first_occurrence_stage_locality k F order hLoc hSupp j hj d hd
    have hSub : ∀ l ∈ d, l ∈ window k c i := by
      intro l hl
      have hlo : i ≤ order.idxOf l.1 := Finset.min'_le ranks _ (Finset.mem_image.mpr ⟨l,hl,rfl⟩)
      have hhi : order.idxOf l.1 ≤ order.idxOf pivot.1 + k := hLocal l hl pivot hPivot
      rw [hRank] at hhi
      exact at_rank_in_window k i c l (hSup l hl) hlo hhi
    let row := (window k c i).filter (fun l => decide (l ∈ d))
    have hrow : row ∈ U := (hU row).mpr (Or.inr ⟨i,hi,List.filter_sublist⟩)
    refine ⟨row,hrow,?_⟩
    ext l
    simp only [row,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨hSub l h,h⟩⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hz
    refine ⟨[],(hU []).mpr (Or.inl rfl),?_⟩
    simp [he]

end PEqualNP.Outside
