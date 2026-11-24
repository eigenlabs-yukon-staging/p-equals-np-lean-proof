import PEqualNP.Outside.UniqueTernaryClauseLowerBound

namespace PEqualNP.Outside.UniqueTernaryCount
open PEqualNP.Search

def names (F : CNF) : List ℕ := F.flatMap (List.map Prod.fst)

theorem names_len (F : CNF) (h : ∀ c ∈ F, c.length = 3) :
    (names F).length = 3*F.length := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have hC := h c (List.mem_cons_self ..)
    have hF := ih (fun cl hc => h cl (List.mem_cons_of_mem _ hc))
    change ((c.map Prod.fst) ++ names F).length = _
    simp only [List.length_append,List.length_map,List.length_cons,hC,hF]
    omega

theorem sum_names (F : CNF) (n : ℕ) (h : ∀ c ∈ F, ∀ l ∈ c, l.1 < n) :
    (∑ i ∈ Finset.range n, (names F).count i) = (names F).length := by
  let M : Multiset ℕ := names F
  have hM : ∀ v ∈ M, v ∈ Finset.range n := by
    intro v hv
    change v ∈ names F at hv
    obtain ⟨c,hc,hm⟩ := List.mem_flatMap.mp hv
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hm
    exact Finset.mem_range.mpr (h c hc l hl)
  simpa only [M,Multiset.coe_count,Multiset.coe_card] using Multiset.sum_count_eq_card hM

theorem degree_sum (F : CNF) (n v : ℕ)
    (hn : v < n)
    (hS : ∀ c ∈ F, c.length = 3 ∧ ∀ l ∈ c, l.1 < n)
    (hD : ∀ i, (names F).count i ≤ 4) (hv : (names F).count v ≤ 3) :
    3*F.length < 4*n := by
  have hSum : (∑ i ∈ Finset.range n, (names F).count i) <
      ∑ _i ∈ Finset.range n, (4:ℕ) := by
    apply Finset.sum_lt_sum
    · exact fun i _ => hD i
    · exact ⟨v,Finset.mem_range.mpr hn,by omega⟩
  have he := sum_names F n (fun c hc => (hS c hc).2)
  have hf := names_len F (fun c hc => (hS c hc).1)
  rw [he,hf] at hSum
  simpa [Nat.mul_comm] using hSum

end PEqualNP.Outside.UniqueTernaryCount

open PEqualNP.Search

theorem PEqualNP.Outside.UniqueTernaryDegreeFourMinimumNames :
    ∀ (n : ℕ) (F : CNF) (terminal : ℕ), 4 ≤ n → terminal < n →
      (∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) →
      (∀ i, (F.flatMap (List.map Prod.fst)).count i ≤ 4) →
      (F.flatMap (List.map Prod.fst)).count terminal ≤ 3 →
      (∃! a : Fin n → Bool,
        CNF.eval (fun i => if h : i < n then a ⟨i,h⟩ else false) F = true) →
      7 ≤ n := by
  intro n F terminal hn ht hs hd hT hu
  have hl := PEqualNP.Outside.UniqueTernaryCount.lower n F hn hs hu
  have hc := PEqualNP.Outside.UniqueTernaryCount.degree_sum F n terminal ht
    (fun c h => ⟨(hs c h).1,(hs c h).2.2⟩) hd hT
  omega
