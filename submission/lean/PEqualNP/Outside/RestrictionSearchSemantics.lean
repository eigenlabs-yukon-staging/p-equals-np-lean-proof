import PEqualNP.Outside.TwoSatGreedyCore
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside.RestrictionSearchSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.FirstWideCollector (Word pack)
open PEqualNP.Outside.TwoSatGreedyCore
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers (restrict sat_restrict_iff)
open PEqualNP.Outside.BackdoorPathCore (cut_eq)
open PEqualNP.Outside.HornRenameMachine (flips)

def state (φ : CNF) (r : Word) (s v : List ℕ) : Word :=
  pack (encodeCNF φ) r (names s) (names v)

def permitted (φ : CNF) (s v : List ℕ) : Prop :=
  (∀ i ∈ v, i ∈ s) ∧ Satisfiable (restrict (valueOf s v) φ)

def covers (φ : CNF) (s : List ℕ) : Prop :=
  ∀ c ∈ φ, ∀ l ∈ c, l.1 ∈ s

private theorem name_enc (φ : CNF) (l : Literal) (r : Word) (s v : List ℕ) :
    name (state φ (encodeLiteral l ++ r) s v) = vcode l.1 := by
  have hlen : (vcode l.1).length ≤ (encodeLiteral l ++ r).length := by
    simp [encodeLiteral_eq]
    omega
  simp only [name, state, cursor, pack, unpairB_pairB, headI_lit]
  rw [show (encodeLiteral l).tail.tail = vcode l.1 by simp [encodeLiteral_eq],
    cut_eq, List.take_of_length_le hlen]

private theorem trial_enc (φ : CNF) (l : Literal) (r : Word) (s v : List ℕ) :
    trial (state φ (encodeLiteral l ++ r) s v) =
      encodeCNF (restrict (valueOf (s ++ [l.1]) v) φ) := by
  unfold trial
  rw [name_enc]
  simp only [problem, chosen, trueNames, state, pack, unpairB_pairB]
  have h : names s ++ vcode l.1 = names (s ++ [l.1]) := by simp [names, List.flatMap_append]
  rw [h, run_enc]

theorem step_lit_known (dec : Word → Bool) (φ : CNF) (l : Literal) (r : Word)
    (s v : List ℕ) (hl : l.1 ∈ s) :
    step dec (state φ (encodeLiteral l ++ r) s v) = state φ r s v := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  have hb : memB (vcode l.1) (names s) = true := (asg_codes s l.1).mpr hl
  unfold step
  dsimp only
  rw [name_enc]
  simp [state, cursor, problem, chosen, trueNames, pack, unpairB_pairB, sel, hn, isEnd_lit,
    bflag, dropI_lit, hb]

theorem step_lit_new (dec : Word → Bool) (φ : CNF) (l : Literal) (r : Word)
    (s v : List ℕ) (hl : l.1 ∉ s) :
    let f := dec (encodeCNF (restrict (valueOf (s ++ [l.1]) v) φ))
    step dec (state φ (encodeLiteral l ++ r) s v) =
      state φ r (s ++ [l.1]) (v ++ if f then [] else [l.1]) := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  have hb : memB (vcode l.1) (names s) = false := by
    cases he : memB (vcode l.1) (names s)
    · rfl
    · exact False.elim (hl ((asg_codes s l.1).mp he))
  unfold step
  dsimp only
  rw [name_enc, trial_enc]
  simp only [names] at hb
  cases h : dec (encodeCNF (restrict (valueOf (s ++ [l.1]) v) φ)) <;>
    simp [state, cursor, problem, chosen, trueNames, pack, unpairB_pairB, sel, hn, isEnd_lit,
      bflag, dropI_lit, hb, h, names, List.flatMap_append]

theorem step_close (dec : Word → Bool) (φ : CNF) (r : Word) (s v : List ℕ) :
    step dec (state φ ([false, false] ++ r) s v) = state φ r s v := by
  simp [step, state, cursor, problem, chosen, trueNames, pack, unpairB_pairB, sel,
    isEnd, bflag, dropI]

theorem step_end (dec : Word → Bool) (φ : CNF) (s v : List ℕ) :
    step dec (state φ [] s v) = state φ [] s v := by
  simp [step, state, cursor, pack, unpairB_pairB, sel]

def hereditary (F : Set CNF) : Prop :=
  ∀ (ρ : ℕ → Option Bool) (φ : CNF), φ ∈ F → restrict ρ φ ∈ F

def correct (F : Set CNF) (dec : Word → Bool) : Prop :=
  ∀ φ ∈ F, Satisfiable φ ↔ dec (encodeCNF φ) = true

theorem extension (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec)
    (φ : CNF) (hF : φ ∈ F) (s v : List ℕ) (i : ℕ)
    (hi : i ∉ s) (h : permitted φ s v) :
    let f := dec (encodeCNF (restrict (valueOf (s ++ [i]) v) φ))
    permitted φ (s ++ [i]) (v ++ if f then [] else [i]) := by
  have hnot : i ∉ v := fun hv => hi (h.1 i hv)
  have hall (σ : Assignment) (hag : ∀ j b, valueOf s v j = some b → σ j = b) :
      ∀ j b, valueOf (s ++ [i]) (v ++ if σ i then [i] else []) j = some b → σ j = b := by
    intro j b hj
    by_cases he : j = i
    · subst j
      cases hs : σ i <;> simpa [valueOf, hnot, hs] using hj
    · apply hag j b
      cases hs : σ i <;> simpa [valueOf, he, hs] using hj
  dsimp only
  cases hf : dec (encodeCNF (restrict (valueOf (s ++ [i]) v) φ))
  · simp only [Bool.false_eq_true, ite_false]
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases List.mem_append.mp hj with hm | hm
      · exact List.mem_append_left _ (h.1 j hm)
      · exact List.mem_append_right _ hm
    · obtain ⟨σ, hs, hag⟩ := (sat_restrict_iff _ _).mp h.2
      have ht : σ i = true := by
        cases hv : σ i
        · have hnew : Satisfiable (restrict (valueOf (s ++ [i]) v) φ) := by
            apply (sat_restrict_iff _ _).mpr
            exact ⟨σ, hs, by simpa [hv] using hall σ hag⟩
          have he := (hd _ (hclosed _ _ hF)).mp hnew
          simp [hf] at he
        · rfl
      apply (sat_restrict_iff _ _).mpr
      exact ⟨σ, hs, by simpa [ht] using hall σ hag⟩
  · simp only [ite_true, List.append_nil]
    refine ⟨fun j hj => List.mem_append_left _ (h.1 j hj), ?_⟩
    exact (hd _ (hclosed _ _ hF)).mpr hf

theorem scan_clause (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec)
    (φ : CNF) (hF : φ ∈ F) (c : Clause) (r : Word) (s v : List ℕ)
    (h : permitted φ s v) :
    ∃ s' v' : List ℕ,
      (step dec)^[c.length] (state φ (c.flatMap encodeLiteral ++ r) s v) = state φ r s' v' ∧
      permitted φ s' v' ∧ (∀ i ∈ s, i ∈ s') ∧ ∀ l ∈ c, l.1 ∈ s' := by
  induction c generalizing s v with
  | nil => exact ⟨s, v, rfl, h, fun _ hi => hi, by simp⟩
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases hl : l.1 ∈ s
    · rw [step_lit_known dec φ l _ s v hl]
      obtain ⟨s', v', he, hp, hm, hc⟩ := ih s v h
      refine ⟨s', v', he, hp, hm, ?_⟩
      intro d hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact hm _ hl
      · exact hc _ hd'
    · rw [step_lit_new dec φ l _ s v hl]
      let f := dec (encodeCNF (restrict (valueOf (s ++ [l.1]) v) φ))
      have he := extension F hclosed dec hd φ hF s v l.1 hl h
      obtain ⟨s', v', ht, hp, hm, hc⟩ := ih (s ++ [l.1]) (v ++ if f then [] else [l.1]) he
      refine ⟨s', v', ht, hp, fun i hi => hm i (by simp [hi]), ?_⟩
      intro d hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact hm _ (by simp)
      · exact hc _ hd'

theorem scan (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec)
    (φ : CNF) (hF : φ ∈ F) (ψ : CNF) (s v : List ℕ)
    (h : permitted φ s v) :
    ∃ s' v' : List ℕ,
      (step dec)^[nIt ψ] (state φ (encodeCNF ψ) s v) = state φ [] s' v' ∧
      permitted φ s' v' ∧ (∀ i ∈ s, i ∈ s') ∧ covers ψ s' := by
  induction ψ generalizing s v with
  | nil => exact ⟨s, v, rfl, h, fun _ hi => hi, by simp [covers]⟩
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = c.flatMap encodeLiteral ++ ([false, false] ++ encodeCNF cs) := by
      simp [encodeCNF, encodeClause, List.append_assoc]
    rw [hn, he, Function.iterate_add_apply, Function.iterate_succ_apply']
    obtain ⟨k, t, hstep, hp, hm, hc⟩ := scan_clause F hclosed dec hd φ hF c _ s v h
    rw [hstep, step_close]
    obtain ⟨s', v', hs, hq, hsub, htail⟩ := ih k t hp
    refine ⟨s', v', hs, hq, fun i hi => hsub i (hm i hi), ?_⟩
    intro d hd' l hl
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hsub _ (hc _ hl)
    · exact htail _ hd' _ hl

theorem solve (F : Set CNF) (hclosed : hereditary F) (dec : Word → Bool)
    (hd : correct F dec)
    (φ ψ : CNF) (hF : φ ∈ F) (hs : Satisfiable φ)
    (inc : ∀ c ∈ φ, ∀ l ∈ c, ∃ d ∈ ψ, ∃ r ∈ d, r.1 = l.1) :
    ∃ v : List ℕ, finish dec (encodeCNF ψ, encodeCNF φ) = names v ∧ CNF.eval (flips v) φ = true := by
  have hp : permitted φ [] [] := by
    refine ⟨by simp, ?_⟩
    apply (sat_restrict_iff _ _).mpr
    obtain ⟨σ, hσ⟩ := hs
    exact ⟨σ, hσ, by simp [valueOf]⟩
  obtain ⟨s, v, he, ha, _, hcover⟩ := scan F hclosed dec hd φ hF ψ [] [] hp
  refine ⟨v, ?_, ?_⟩
  · have hn := nIt_le ψ
    change trueNames ((step dec)^[(encodeCNF ψ).length] (state φ (encodeCNF ψ) [] [])) = _
    rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, he,
      Function.iterate_fixed (step_end dec φ s v)]
    simp [trueNames, state, pack, unpairB_pairB]
  · obtain ⟨σ, hσ, hag⟩ := (sat_restrict_iff _ _).mp ha.2
    apply List.all_eq_true.mpr
    intro c hc
    have ht := List.all_eq_true.mp hσ c hc
    obtain ⟨l, hl, hgood⟩ := List.any_eq_true.mp ht
    obtain ⟨d, hd', r, hr, heq⟩ := inc c hc l hl
    have hm : l.1 ∈ s := heq ▸ hcover d hd' r hr
    have hflip : σ l.1 = flips v l.1 := by
      apply hag l.1
      simp [valueOf, flips, hm]
    exact List.any_eq_true.mpr ⟨l, hl, by simpa [Literal.eval, hflip] using hgood⟩

end PEqualNP.Outside.RestrictionSearchSemantics
