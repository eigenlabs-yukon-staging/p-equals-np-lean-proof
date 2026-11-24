import PEqualNP.Outside.ShortestWidthPathComplete
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Library.L030

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.ShortestWidthPathCore (query query_cpt)
open PEqualNP.Outside.ShortestWidthPathSemantics (query_sound)
open PEqualNP.Outside.ShortestWidthPathComplete (complete_query)
open PEqualNP.Outside.ShortWideCollector (shortest shortest_some shortest_none)
open PEqualNP.Outside.PartialAssignmentFacts (assignment)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)

private theorem cpt_nonempty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => !x.isEmpty) := by
  let move : Bool → Bool → Bool × Option Bool := fun _ _ => (true, none)
  have ht (l : List Bool) : fstRun move (fun b => some b) true l = [true] := by
    induction l with
    | nil => rfl
    | cons b l ih => simp [fstRun, move, ih]
  refine fst_polyTime _ _ _ move (fun b => some b) false ?_
  intro l
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, move, ht, Computability.encodeBool]

private theorem wfFlag_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

theorem PEqualNP.Outside.SmallWeakBackdoorShortestWidthSATInP (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF,
        (∃ (a : Finset ℕ) (σ : Assignment) (w : ℕ),
          CNF.eval σ φ = true ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           IsKCNF 2 (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone))) ∧
          (∀ b ⊆ a,
            let ρ := fun i : ℕ => if i ∈ b then some (σ i) else none
            let residual : CNF := φ.filterMap fun d =>
              if d.any (fun l => ρ l.1 == some l.2) then none
              else some (d.filter fun l => (ρ l.1).isNone)
            IsKCNF 2 residual ∨ ∃ c ∈ residual, 2 < List.length c ∧ List.length c ≤ w) ∧
          2 ^ (((w - 1).size + 1) * a.card) ≤ p.eval (encodeCNF φ).length) →
        encodeCNF φ ∈ L := by
  obtain ⟨dec, hd, hc⟩ := L030
  let R : Set (List Bool × List Bool) := {q | query q ∈ KSAT 2}
  let test : List Bool × List Bool → Bool := fun q => dec (query q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hd (query q)
  have htime : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp query_cpt hc
  obtain ⟨select, hselect, hfind⟩ :=
    EnumeratingSelector.select_bounded R p (Polynomial.C 2 * p) ⟨test, htest, htime⟩
  let answer (x : List Bool) := !(sel (bflag (wfB x)) [] (bflag (test (x, select x)))).isEmpty
  let L : Language Bool := {x | answer x = true}
  have hanswer : ∀ x, x ∈ L ↔ wfB x = true ∧ test (x, select x) = true := by
    intro x
    change answer x = true ↔ wfB x = true ∧ test (x, select x) = true
    cases h : wfB x <;> cases ht : test (x, select x) <;>
      simp [L, answer, h, ht, sel, bflag]
  have htimeL : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool answer := by
    have hf := cpt_bitFlag (cpt_comp (cpt_pair cpt_id hselect) htime)
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const []) hf) cpt_nonempty
    exact h
  have hsound (φ : CNF) (h : encodeCNF φ ∈ L) : Satisfiable φ :=
    query_sound φ _ ((htest _).mpr ((hanswer _).mp h).2)
  refine ⟨L, ⟨answer, fun _ => Iff.rfl, htimeL⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp ((hanswer x).mp hx).1
    exact ⟨φ, rfl, hsound φ hx⟩
  · rintro φ ⟨a, σ, w, hσ, ha, hw, hb⟩
    refine (hanswer _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, ?_⟩
    have hwidth (b : Finset ℕ) (hb : b ⊆ a) (c : Clause)
        (hc : shortest (restrict (assignment b σ) φ) = some c) : c.length ≤ w := by
      rcases hw b hb with htwo | ⟨d, hd, hwide, hlen⟩
      · have hnone := (shortest_none (restrict (assignment b σ) φ)).mpr htwo
        rw [hc] at hnone
        contradiction
      · exact ((shortest_some hc).2.2 d hd hwide).trans hlen
    obtain ⟨b, hlen, hmem⟩ := complete_query φ a σ w hwidth hσ ha
    have hpow : 2 ^ b.length ≤ p.eval (encodeCNF φ).length :=
      (Nat.pow_le_pow_right (by decide) hlen).trans hb
    have hblen : b.length ≤ p.eval (encodeCNF φ).length := Nat.lt_two_pow_self.le.trans hpow
    have hlim : 2 ^ (b.length + 1) ≤ (Polynomial.C 2 * p).eval (encodeCNF φ).length := by
      rw [pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hpow
    have hrank := (BoundedEnumeration.idx_bound b).trans hlim
    exact (htest _).mp (hfind (encodeCNF φ)
      ⟨b, ⟨hblen, hmem⟩, (Nat.le_add_right _ _).trans hrank⟩).2
