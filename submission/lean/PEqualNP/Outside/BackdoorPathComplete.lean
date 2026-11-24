import PEqualNP.Outside.BackdoorPathSemantics

namespace PEqualNP.Outside.BackdoorPathComplete

open PEqualNP.Search
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathMachine PEqualNP.Outside.BackdoorPathSemantics
open PEqualNP.Outside.TripleObstructionSemantics (Triple firstBad firstBad_none)
open PEqualNP.Outside.BackdoorBranch
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf)
open PEqualNP.Outside.RestrictCnfHelpers

theorem step_follow (φ : CNF) (k : List ℕ) (σ : Assignment) (t : Triple)
    (h : firstBad k φ = some t) (j : Fin 3) (tail : Word) :
    let i := selectedName t j
    let k' := k ++ [i]
    step (pack (encodeCNF φ) (names k) (names (k.filter σ))
      (branchBits j (σ i) ++ tail)) =
      pack (encodeCNF φ) (names k') (names (k'.filter σ)) tail := by
  dsimp only
  rw [step_next _ _ _ _ t h]
  simp only [branch_index, branch_value, branch_tail, List.filter_append]
  cases hi : σ (selectedName t j) <;> simp [hi]

theorem path_exists (φ : CNF) (a : Finset ℕ) (σ : Assignment) (hs : strong a φ)
    (budget : ℕ) (k : List ℕ) (hk : ∀ i ∈ k, i ∈ a)
    (hb : (a \ k.toFinset).card ≤ budget) :
    ∃ rounds ≤ budget, ∃ b : Word, ∃ k' : List ℕ,
      b.length = 3 * rounds ∧ firstBad k' φ = none ∧
      step^[rounds] (pack (encodeCNF φ) (names k) (names (k.filter σ)) b) =
        pack (encodeCNF φ) (names k') (names (k'.filter σ)) [] := by
  induction budget using Nat.strong_induction_on generalizing k with
  | ind n ih =>
    cases h : firstBad k φ with
    | none =>
      exact ⟨0, Nat.zero_le _, [], k, rfl, h, rfl⟩
    | some t =>
      obtain ⟨j, hj⟩ := triple_hits h hs hk
      let i := selectedName t j
      let new := k ++ [i]
      have hnot : i ∉ k := (triple_member h j).1
      have hnew : ∀ v ∈ new, v ∈ a := by
        intro v hv
        simp only [new, List.mem_append, List.mem_singleton] at hv
        rcases hv with hm | rfl
        · exact hk v hm
        · exact hj
      have hleft : (a \ new.toFinset).card < n :=
        (left_decreases a k i hj hnot).trans_le hb
      obtain ⟨rounds, hrounds, tail, k', hlen, hfinish, hstep⟩ :=
        ih (a \ new.toFinset).card hleft new hnew le_rfl
      refine ⟨rounds + 1, by omega, branchBits j (σ i) ++ tail, k', ?_, hfinish, ?_⟩
      · simp only [branchBits, List.length_append, List.length_cons, List.length_nil, hlen]
        omega
      · rw [Function.iterate_succ_apply, step_follow φ k σ t h j tail]
        exact hstep

theorem complete_query (φ : CNF) (a : Finset ℕ) (hs : strong a φ) (hSAT : Satisfiable φ) :
    ∃ b : Word, b.length ≤ 3 * a.card ∧ query (encodeCNF φ, b) ∈ KSAT 2 := by
  obtain ⟨σ, hσ⟩ := hSAT
  obtain ⟨rounds, hr, b, k, hlen, hdone, hstep⟩ :=
    path_exists φ a σ hs a.card [] (by simp) (by simp)
  refine ⟨b, by omega, ?_⟩
  have hn : rounds ≤ b.length := by omega
  have he : endState (encodeCNF φ, b) =
      pack (encodeCNF φ) (names k) (names (k.filter σ)) [] := by
    change step^[b.length] (pack (encodeCNF φ) [] [] b) = _
    change step^[rounds] (pack (encodeCNF φ) [] [] b) = _ at hstep
    rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, hstep,
      Function.iterate_fixed (step_done φ k (k.filter σ) [] hdone)]
  have hp : query (encodeCNF φ, b) = encodeCNF (restrict (valueOf k (k.filter σ)) φ) := by
    unfold query
    rw [he, finish_enc]
  rw [hp]
  refine ⟨restrict (valueOf k (k.filter σ)) φ, ?_, rfl, ?_⟩
  · apply restrict_width
    intro c hc
    have e : (fun l : Literal => (valueOf k (k.filter σ) l.1).isNone) =
        (fun l : Literal => decide (l.1 ∉ k)) := by
      funext l
      by_cases hm : l.1 ∈ k <;> simp [valueOf, hm]
    rw [e]
    exact (firstBad_none k φ).mp hdone c hc
  · apply (sat_restrict_iff _ _).mpr
    refine ⟨σ, hσ, ?_⟩
    intro i v hv
    by_cases hm : i ∈ k
    · cases he : σ i <;> simpa [valueOf, hm, List.mem_filter, he] using hv
    · simp [valueOf, hm] at hv

end PEqualNP.Outside.BackdoorPathComplete
