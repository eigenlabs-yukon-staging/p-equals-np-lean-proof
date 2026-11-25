import PEqualNP.Outside.DavisPutnamElimination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace PEqualNP.Outside

def eliminationLocality (index : ℕ → ℕ) (k : ℕ) (F : Set NatClause) : Prop :=
  ∀ c ∈ F, ∀ p ∈ c, ∀ q ∈ c, index p.1 ≤ index q.1 + k

theorem eliminationLocality_step (index : ℕ → ℕ) (k x : ℕ) (F : Set NatClause)
    (hl : eliminationLocality index k F) (hmin : ∀ c ∈ F, ∀ l ∈ c, index x ≤ index l.1) :
    eliminationLocality index k (eliminateVariable x F) := by
  intro c hc
  rcases hc with ⟨hF,_,_⟩ | ⟨P,hP,N,hN,hp,_,hn,_,rfl⟩
  · exact hl c hF
  · have hbound (l : ℕ × Bool) (hm : l ∈ P.erase (x,true) ∪ N.erase (x,false)) :
        index x ≤ index l.1 ∧ index l.1 ≤ index x + k := by
      rcases Finset.mem_union.mp hm with hm | hm
      · have h := (Finset.mem_erase.mp hm).2
        exact ⟨hmin P hP l h,hl P hP l h (x,true) hp⟩
      · have h := (Finset.mem_erase.mp hm).2
        exact ⟨hmin N hN l h,hl N hN l h (x,false) hn⟩
    intro p hp' q hq'
    have h1 := (hbound p hp').2
    have h2 := (hbound q hq').1
    omega

theorem signed_locality_width (k : ℕ) (c : NatClause)
    (hl : ∀ p ∈ c, ∀ q ∈ c, p.1 ≤ q.1 + k) : c.card ≤ 2 * (k+1) := by
  by_cases hz : c.Nonempty
  · let vars := c.image Prod.fst
    have hv : vars.Nonempty := hz.image _
    let v := vars.min' hv
    obtain ⟨q,hq,hqv⟩ := Finset.mem_image.mp (Finset.min'_mem vars hv)
    have hsub : c ⊆ (Finset.Icc v (v+k)) ×ˢ (Finset.univ : Finset Bool) := by
      intro p hp
      rw [Finset.mem_product,Finset.mem_Icc]
      have hmin : v ≤ p.1 := Finset.min'_le vars _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
      have hmax := hl p hp q hq
      rw [hqv] at hmax
      exact ⟨⟨hmin,hmax⟩,Finset.mem_univ _⟩
    calc
      c.card ≤ ((Finset.Icc v (v+k)) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_le_card hsub
      _ = 2 * (k+1) := by simp [Finset.card_product,Nat.card_Icc,Nat.mul_comm,Nat.add_assoc]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hz]

/-- Ascending elimination of a formula with bounded co-occurrence distance
preserves that distance and bounds all signed clause widths. -/
theorem LocalityEliminationWidth (k : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause ℕ)) (order : List ℕ) :
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    order.Pairwise (· ≤ ·) →
    (∀ c ∈ F, ∀ p ∈ c, ∀ q ∈ c, p.1 ≤ q.1 + k) →
    (∀ c ∈ F, ∀ l ∈ c, l.1 ∈ order) →
    ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl eliminate F,
      (∀ p ∈ c, ∀ q ∈ c, p.1 ≤ q.1 + k) ∧ Finset.card c ≤ 2 * (k+1) := by
  dsimp only
  intro hord hl hs
  change eliminationLocality id k F at hl
  change ∀ j ≤ order.length, ∀ c ∈ (order.take j).foldl (fun G x => eliminateVariable x G) F,
    (∀ p ∈ c, ∀ q ∈ c, p.1 ≤ q.1 + k) ∧ Finset.card c ≤ 2 * (k+1)
  induction order generalizing F with
  | nil =>
    intro j hj c hc
    have he : j = 0 := by simpa using hj
    subst j
    exact ⟨hl c hc,signed_locality_width k c (hl c hc)⟩
  | cons x xs ih =>
    intro j hj c hc
    cases j with
    | zero => exact ⟨hl c hc,signed_locality_width k c (hl c hc)⟩
    | succ j =>
      have hmin : ∀ d ∈ F, ∀ l ∈ d, x ≤ l.1 := by
        intro d hd l hl'
        rcases List.mem_cons.mp (hs d hd l hl') with h | h
        · exact h.ge
        · exact (List.pairwise_cons.mp hord).1 _ h
      have htail : ∀ d ∈ eliminateVariable x F, ∀ l ∈ d, l.1 ∈ xs := by
        intro d hd l hl'
        obtain ⟨hne,c,hc,hl'⟩ := eliminate_support hd l hl'
        exact (List.mem_cons.mp (hs c hc l hl')).resolve_left hne
      exact ih (eliminateVariable x F) (List.pairwise_cons.mp hord).2
        htail (eliminationLocality_step id k x F hl hmin) j (by simpa using hj) c hc


end PEqualNP.Outside
