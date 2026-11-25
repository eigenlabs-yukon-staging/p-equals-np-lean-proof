import PEqualNP.Library.L030
import PEqualNP.Library.L055
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Outside.MeasuredTripleSelections

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Search

private abbrev Triple := Literal × Literal × Literal

private def choose (groups : List Triple) (seed : List Bool) : List Literal :=
  (List.range groups.length).map (fun i =>
    let (a,b,c) := groups[i]?.getD ((0,false),(0,false),(0,false))
    if seed.getD (2*i) false then a else if seed.getD (2*i+1) false then b else c)

private theorem choose_cons (a b c : Literal) (groups : List Triple) (seed : List Bool) :
    choose ((a,b,c) :: groups) seed =
      (if seed.headD false then a else if seed.tail.headD false then b else c) ::
        choose groups seed.tail.tail := by
  unfold choose
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [List.getElem?_cons_zero, Option.getD_some, Nat.mul_zero, Nat.zero_add,
    List.headD_eq_getD, List.cons.injEq]
  constructor
  · simp [List.getD, List.getElem?_tail]
    rfl
  · congr 1
    funext i
    simp [List.getD, List.getElem?_tail, Nat.mul_succ, Nat.add_assoc]

private def clauses (groups : List Triple) : CNF :=
  groups.map (fun group => [group.1,group.2.1,group.2.2])

private theorem choices_sound (σ : Assignment) (groups : List Triple) (seed : List Bool)
    (h : ∀ l ∈ choose groups seed, l.eval σ = true) :
    (clauses groups).eval σ = true := by
  induction groups generalizing seed with
  | nil => rfl
  | cons group groups ih =>
      rcases group with ⟨a,b,c⟩
      rw [choose_cons] at h
      have hhead := h _ List.mem_cons_self
      have htail := ih seed.tail.tail (fun l hl => h l (List.mem_cons_of_mem _ hl))
      simp only [clauses, List.map_cons, CNF.eval, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, htail⟩
      unfold Clause.eval
      rw [List.any_eq_true]
      refine ⟨_, ?_, hhead⟩
      split
      · exact List.mem_cons_self
      · split
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem choices_complete (σ : Assignment) (groups : List Triple)
    (h : (clauses groups).eval σ = true) :
    ∃ seed : List Bool, seed.length = 2 * groups.length ∧
      ∀ l ∈ choose groups seed, l.eval σ = true := by
  induction groups with
  | nil => exact ⟨[], rfl, by simp [choose]⟩
  | cons group groups ih =>
      rcases group with ⟨a,b,c⟩
      simp only [clauses, List.map_cons, CNF.eval, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨seed, hlen, hgo⟩ := ih h.2
      have ha : ∃ l ∈ [a,b,c], l.eval σ = true := List.any_eq_true.mp h.1
      obtain ⟨l, hl, ht⟩ := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · refine ⟨true :: false :: seed, by simp [hlen, Nat.mul_succ], ?_⟩
        simpa [choose_cons, List.mem_cons, or_imp, forall_and, ht] using hgo
      · refine ⟨false :: true :: seed, by simp [hlen, Nat.mul_succ], ?_⟩
        simpa [choose_cons, List.mem_cons, or_imp, forall_and, ht] using hgo
      · refine ⟨false :: false :: seed, by simp [hlen, Nat.mul_succ], ?_⟩
        simpa [choose_cons, List.mem_cons, or_imp, forall_and, ht] using hgo

private def unitWords (groups : List Triple) : List (List Bool × List Bool × List Bool) :=
  groups.map (fun group => (encodeClause [group.1], encodeClause [group.2.1], encodeClause [group.2.2]))

private def packedGroups (groups : List Triple) : List Bool :=
  (unitWords groups).foldr (fun group rest => pairB (pairB group.1 (pairB group.2.1 group.2.2)) rest) []

private def units (ls : List Literal) : CNF := ls.map (fun l => [l])

private theorem units_sat (σ : Assignment) (ls : List Literal) :
    (units ls).eval σ = true ↔ ∀ l ∈ ls, l.eval σ = true := by
  simp [units, CNF.eval, Clause.eval, List.all_eq_true]

private theorem unitWords_selected (groups : List Triple) (seed : List Bool) :
    ((List.range (unitWords groups).length).flatMap (fun i =>
      let group := (unitWords groups)[i]?.getD ([],[],[])
      if seed.getD (2*i) false then group.1 else if seed.getD (2*i+1) false then group.2.1 else group.2.2)) =
      encodeCNF (units (choose groups seed)) := by
  unfold encodeCNF units choose
  rw [List.map_map, List.flatMap_map]
  simp only [unitWords, List.length_map]
  apply List.flatMap_congr
  intro i hi
  have his : i < groups.length := List.mem_range.mp hi
  have hget : groups[i]? = some groups[i] := List.getElem?_eq_getElem his
  simp only [Function.comp_apply, List.getElem?_map, hget, Option.map_some, Option.getD_some]
  rcases groups[i] with ⟨a,b,c⟩
  split
  · rfl
  · split <;> rfl

private theorem kcnf_units (φ : CNF) (hφ : IsKCNF 2 φ) (ls : List Literal) :
    IsKCNF 2 (φ ++ units ls) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hφ c hc
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
    simp

/-- A mixed formula with a 2-CNF base and polynomially many selections of one literal
from each additional three-literal clause can be decided by the pinned 2-SAT machine. -/
theorem ThreeClauseBranching2SAT (q : Polynomial ℕ) :
    ∃ D : Language Bool, D ∈ P ∧
      ∀ (φ : CNF) (groups : List (Literal × Literal × Literal)),
        let packed := (groups.map (fun group =>
          (encodeClause [group.1], encodeClause [group.2.1], encodeClause [group.2.2]))).foldr (fun group rest =>
            let bc := List.replicate group.2.1.length true ++ false :: (group.2.1 ++ group.2.2)
            let abc := List.replicate group.1.length true ++ false :: (group.1 ++ bc)
            List.replicate abc.length true ++ false :: (abc ++ rest)) []
        let query := List.replicate (encodeCNF φ).length true ++ false :: (encodeCNF φ ++ packed)
        IsKCNF 2 φ → 2 ^ (2 * groups.length + 1) ≤ q.eval query.length →
          (query ∈ D ↔ Satisfiable (φ ++ groups.map (fun group => [group.1,group.2.1,group.2.2]))) := by
  obtain ⟨select, hselect, hformula⟩ := MeasuredTripleSelections
  obtain ⟨sat, hsat, hsatC⟩ := L030
  let R : Set (List Bool × List Bool) := {z | z.2 ∈ KSAT 2}
  have hR : DecidableInPolyTime encodePair R :=
    ⟨fun z => sat z.2, fun z => hsat z.2, cpt_comp cpt_snd hsatC⟩
  let clock := fun x : List Bool => List.replicate (q.eval x.length) true
  let gen := fun z : List Bool × List Bool =>
    (unpairB z.2).1 ++ select ((unpairB z.2).2, cand z.1.length)
  have hcand : ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x => cand x.length) :=
    cpt_iterGrow bf_cpt_succB 1 bf_succB_length cpt_id (cpt_const [])
  have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) gen := by
    have hA := cpt_comp cpt_snd cpt_unpairB1
    have hB := cpt_comp cpt_snd cpt_unpairB2
    have hseed := cpt_comp (g := fun l : List Bool => cand l.length) cpt_fst hcand
    exact cpt_comp (cpt_pairG hA (cpt_comp (cpt_pairG hB hseed) hselect)) cpt_append
  let D : Language Bool := {x | ∃ i < (clock x).length, (x, gen (List.replicate i true, x)) ∈ R}
  refine ⟨D, IndexedWitnessProjection R hR clock (L055 q) gen hg, fun φ groups => ?_⟩
  dsimp only
  change IsKCNF 2 φ →
    2 ^ (2 * groups.length + 1) ≤ q.eval (pairB (encodeCNF φ) (packedGroups groups)).length →
    (pairB (encodeCNF φ) (packedGroups groups) ∈ D ↔ Satisfiable (φ ++ clauses groups))
  intro hφ hbudget
  let x := pairB (encodeCNF φ) (packedGroups groups)
  have hsel (seed : List Bool) :
      select (packedGroups groups, seed) = encodeCNF (units (choose groups seed)) :=
    (hformula (unitWords groups) seed).trans (unitWords_selected groups seed)
  have hgen (i : ℕ) :
      gen (List.replicate i true, x) = encodeCNF (φ ++ units (choose groups (cand i))) := by
    simp only [gen, x, unpairB_pairB, List.length_replicate, hsel, encodeCNF, List.flatMap_append]
  have heval (σ : Assignment) (φ ψ : CNF) :
      (φ ++ ψ).eval σ = true ↔ φ.eval σ = true ∧ ψ.eval σ = true := by
    simp [CNF.eval, List.all_append]
  change (∃ i < (clock x).length, gen (List.replicate i true, x) ∈ KSAT 2) ↔ _
  constructor
  · rintro ⟨i, _, hi⟩
    rw [hgen] at hi
    obtain ⟨ψ, _, henc, σ, hs⟩ := hi
    have hψ := PEqualNP.Library.SearchHelpers.encodeCNF_injective henc
    subst ψ
    obtain ⟨hbase, hunit⟩ := (heval _ _ _).mp hs
    exact ⟨σ, (heval _ _ _).mpr ⟨hbase, choices_sound σ groups _ ((units_sat _ _).mp hunit)⟩⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨hbase, hclauses⟩ := (heval _ _ _).mp hσ
    obtain ⟨seed, hlen, hseed⟩ := choices_complete σ groups hclauses
    refine ⟨idx seed, ?_, ?_⟩
    · have hi := idx_bound seed
      rw [hlen] at hi
      simp only [clock, List.length_replicate, x]
      omega
    · rw [hgen, cand_idx]
      exact ⟨_, kcnf_units φ hφ _, rfl, σ, (heval _ _ _).mpr ⟨hbase, (units_sat _ _).mpr hseed⟩⟩

end PEqualNP.Outside
