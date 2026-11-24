import PEqualNP.Outside.AdaptiveWidthExactPath
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Library.L030

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.AdaptiveWidthPathCore (query query_cpt)
open PEqualNP.Outside.AdaptiveWidthPathSemantics (query_sound)
open PEqualNP.Outside.AdaptiveWidthExactPath (visitedNames valid cost complete)
open PEqualNP.Outside.FirstWideClause (firstWide firstWide_none)
open PEqualNP.Outside.PartialAssignmentFacts (assignment valueOf_filter)
open PEqualNP.Outside.RestrictCnfHelpers (restrict)
open PEqualNP.Outside.WeakWideMachine (bad)
open PEqualNP.Outside.AdaptiveWidthPathSemantics (digits)

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

theorem PEqualNP.Outside.SmallWeakBackdoorPathBudgetSATInP (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF,
        (∃ (σ : Assignment) (path : List (Clause × Literal)),
          CNF.eval σ φ = true ∧
          (∀ i v, path[i]? = some v →
            let k := (path.take i).map (fun q => q.2.1)
            let ρ := fun x : ℕ => if x ∈ k then some (σ x) else none
            ((show CNF from φ.filterMap fun d =>
              if d.any (fun l => ρ l.1 == some l.2) then none
              else some (d.filter fun l => (ρ l.1).isNone))).find?
                (fun d => decide (2 < d.length)) = some v.1 ∧ v.2 ∈ v.1) ∧
          (let k := path.map (fun q => q.2.1)
           let ρ := fun x : ℕ => if x ∈ k then some (σ x) else none
           IsKCNF 2 (φ.filterMap fun d =>
             if d.any (fun l => ρ l.1 == some l.2) then none
             else some (d.filter fun l => (ρ l.1).isNone))) ∧
          2 ^ (path.map (fun v => (v.1.length - 1).size + 1)).sum ≤ p.eval (encodeCNF φ).length) →
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
  · rintro φ ⟨σ, path, hσ, hpath, hweak, hb⟩
    refine (hanswer _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, ?_⟩
    have hrho (k : List ℕ) : assignment k.toFinset σ =
        (fun x : ℕ => if x ∈ k then some (σ x) else none) := by
      funext x
      simp only [assignment, List.mem_toFinset]
    have hvalid : valid φ σ [] path := by
      intro i v hi
      simp only [List.nil_append]
      rw [bad, valueOf_filter, hrho, firstWide, restrict]
      exact hpath i v hi
    have hdone : bad φ (visitedNames path) ((visitedNames path).filter σ) = none := by
      rw [bad, valueOf_filter, hrho]
      apply (firstWide_none _).mpr
      exact hweak
    obtain ⟨b, hlen, hmem⟩ := complete φ σ path hσ hvalid hdone
    have hpow : 2 ^ b.length ≤ p.eval (encodeCNF φ).length := by
      rw [hlen]
      exact hb
    have hblen : b.length ≤ p.eval (encodeCNF φ).length := Nat.lt_two_pow_self.le.trans hpow
    have hlim : 2 ^ (b.length + 1) ≤ (Polynomial.C 2 * p).eval (encodeCNF φ).length := by
      rw [pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hpow
    have hrank := (BoundedEnumeration.idx_bound b).trans hlim
    exact (htest _).mp (hfind (encodeCNF φ)
      ⟨b, ⟨hblen, hmem⟩, (Nat.le_add_right _ _).trans hrank⟩).2
