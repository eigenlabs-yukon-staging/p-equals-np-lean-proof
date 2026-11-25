import PEqualNP.Library.L016
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Outside.CNFThreeClausePacking
import PEqualNP.Outside.ThreeClauseBranching2SAT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

private abbrev Triple := Literal × Literal × Literal

private def small (φ : CNF) : CNF := (φ.filter (fun c => c.length ≤ 2)).reverse

private def triples (φ : CNF) : List Triple :=
  (φ.filterMap (fun c => if c.length = 3 then
    some (c.getD 0 (0,false), c.getD 1 (0,false), c.getD 2 (0,false)) else none)).reverse

private def clauseOf (g : Triple) : Clause := [g.1, g.2.1, g.2.2]

private def unitGroup (g : Triple) : List Bool :=
  pairB (encodeClause [g.1]) (pairB (encodeClause [g.2.1]) (encodeClause [g.2.2]))

private def packed (gs : List Triple) : List Bool :=
  gs.foldr (fun g r => pairB (unitGroup g) r) []

private theorem packed_append (as bs : List Triple) :
    (packed (as ++ bs)).length = (packed as).length + (packed bs).length := by
  induction as with
  | nil => simp [packed]
  | cons a as ih =>
      change (pairB (unitGroup a) (packed (as ++ bs))).length =
        (pairB (unitGroup a) (packed as)).length + (packed bs).length
      rw [pairB_length, pairB_length, ih]
      omega

private theorem clause_len_le_group (a b c : Literal) :
    (encodeClause [a,b,c]).length ≤ (packed [(a,b,c)]).length := by
  change _ ≤ (pairB (unitGroup (a,b,c)) []).length
  simp only [unitGroup, pairB_length, encodeClause, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.nil_append, List.length_append, List.length_cons, List.length_nil]
  omega

private theorem size_bound (φ : CNF) (hφ : IsKCNF 3 φ) :
    (encodeCNF φ).length ≤ (encodeCNF (small φ)).length + (packed (triples φ)).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
      have hct := hφ c List.mem_cons_self
      have ht : IsKCNF 3 φ := fun d hd => hφ d (List.mem_cons_of_mem _ hd)
      have hlen := ih ht
      have hrec : (encodeCNF (c :: φ)).length = (encodeClause c).length + (encodeCNF φ).length := by
        simp [encodeCNF]
      rw [hrec]
      by_cases hcs : c.length ≤ 2
      · have hc3 : c.length ≠ 3 := by omega
        have hsm : small (c :: φ) = small φ ++ [c] := by simp [small, hcs]
        have htr : triples (c :: φ) = triples φ := by simp [triples, hc3]
        rw [hsm, htr]
        simp only [encodeCNF, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.length_append] at hlen ⊢
        omega
      · have hc3 : c.length = 3 := by omega
        have hsm : small (c :: φ) = small φ := by simp [small, hcs]
        obtain ⟨a,b,d,rfl⟩ : ∃ a b d : Literal, c = [a,b,d] := by
          rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩
          · simp at hc3
          · simp at hc3
          · simp at hc3
          · exact ⟨a,b,d,rfl⟩
          · simp at hc3
        have htr : triples ([a,b,d] :: φ) = triples φ ++ [(a,b,d)] := by simp [triples]
        rw [hsm, htr, packed_append]
        have hg := clause_len_le_group a b d
        omega

private theorem partition_eval (φ : CNF) (hφ : IsKCNF 3 φ) (σ : Assignment) :
    φ.eval σ = true ↔ (small φ ++ (triples φ).map clauseOf).eval σ = true := by
  have hp (c : Clause) : c ∈ φ ↔ c ∈ small φ ∨ c ∈ (triples φ).map clauseOf := by
    constructor
    · intro hc
      by_cases hlen : c.length ≤ 2
      · exact Or.inl (by simp [small, hc, hlen])
      · have hc3 := hφ c hc
        have hc3' : c.length = 3 := by omega
        obtain ⟨a,b,d,rfl⟩ : ∃ a b d : Literal, c = [a,b,d] := by
          rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩
          · simp at hc3'
          · simp at hc3'
          · simp at hc3'
          · exact ⟨a,b,d,rfl⟩
          · simp at hc3'
        right
        refine List.mem_map.mpr ⟨(a,b,d), ?_, rfl⟩
        simp only [triples, List.mem_reverse]
        exact List.mem_filterMap.mpr ⟨[a,b,d], hc, by simp⟩
    · rintro (hc | hc)
      · exact (List.mem_filter.mp (List.mem_reverse.mp hc)).1
      · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hc
        have hg' := List.mem_reverse.mp hg
        obtain ⟨d,hd,hs⟩ := List.mem_filterMap.mp hg'
        split at hs
        · rename_i hlen
          obtain ⟨a,b,c,rfl⟩ : ∃ a b c : Literal, d = [a,b,c] := by
            rcases d with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩
            · simp at hlen
            · simp at hlen
            · simp at hlen
            · exact ⟨a,b,c,rfl⟩
            · simp at hlen
          simp at hs
          subst g
          exact hd
        · simp at hs
  simp only [CNF.eval, List.all_eq_true, List.mem_append]
  constructor
  · intro h c hc
    exact h c ((hp c).mpr hc)
  · intro h c hc
    exact h c ((hp c).mp hc)

private theorem count_triples (φ : CNF) :
    (triples φ).length = (φ.filter (fun c => c.length = 3)).length := by
  rw [triples, List.length_reverse]
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      by_cases h : c.length = 3 <;> simpa [h] using ih

/-- There is a reference P decider agreeing with 3-SAT on every canonical 3-CNF
whose number of ternary clauses has polynomially bounded choice space. -/
theorem LogarithmicThreeClauseSAT (q : Polynomial ℕ) :
    ∃ D : Language Bool, D ∈ P ∧ ∀ φ : CNF, IsKCNF 3 φ →
      2 ^ (2 * (φ.filter (fun c => c.length = 3)).length + 1) ≤ q.eval (encodeCNF φ).length →
        (encodeCNF φ ∈ D ↔ Satisfiable φ) := by
  obtain ⟨pack, hpack, hshape⟩ := CNFThreeClausePacking
  obtain ⟨D, hD, hdec⟩ := ThreeClauseBranching2SAT q
  let target : Language Bool := {s | pack s ∈ D}
  have htarget : target ∈ P := L016 target D ⟨pack, hpack, fun _ => Iff.rfl⟩ hD
  refine ⟨target, htarget, fun φ hφ hbudget => ?_⟩
  have hsmall : IsKCNF 2 (small φ) := by
    intro c hc
    have hm := (List.mem_filter.mp (List.mem_reverse.mp hc)).2
    simpa using hm
  have hcount := count_triples φ
  have hmono := eval_mono q (show (encodeCNF φ).length ≤
      (pairB (encodeCNF (small φ)) (packed (triples φ))).length by
    rw [pairB_length]
    have := size_bound φ hφ
    omega)
  have hbudget' : 2 ^ (2 * (triples φ).length + 1) ≤
      q.eval (pairB (encodeCNF (small φ)) (packed (triples φ))).length := by
    rw [hcount]
    exact hbudget.trans hmono
  have hsame : pack (encodeCNF φ) = pairB (encodeCNF (small φ)) (packed (triples φ)) :=
    hshape φ hφ
  have hdec' : pairB (encodeCNF (small φ)) (packed (triples φ)) ∈ D ↔
      Satisfiable (small φ ++ (triples φ).map clauseOf) := by
    have hroute := hdec (small φ) (triples φ) hsmall
    dsimp only at hroute
    simp only [List.foldr_map] at hroute
    change 2 ^ (2 * (triples φ).length + 1) ≤
      q.eval (pairB (encodeCNF (small φ)) (packed (triples φ))).length → _ at hroute
    exact hroute hbudget'
  change pack (encodeCNF φ) ∈ D ↔ Satisfiable φ
  rw [hsame, hdec']
  exact exists_congr (fun σ => (partition_eval φ hφ σ).symm)

end PEqualNP.Outside
