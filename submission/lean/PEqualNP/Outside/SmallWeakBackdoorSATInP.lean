import PEqualNP.Outside.WeakWidthComplete
import PEqualNP.Outside.EnumeratingSelector
import PEqualNP.Library.L030

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.WeakWidthMachine (query query_cpt)
open PEqualNP.Outside.WeakWidthMachine (query_sound)
open PEqualNP.Outside.WeakWidthComplete (complete_query)

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

theorem PEqualNP.Outside.SmallWeakBackdoorSATInP (digits : ℕ) (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF, IsKCNF (2 ^ digits) φ →
        (∃ (a : Finset ℕ) (σ : Assignment),
          CNF.eval σ φ = true ∧
          (let ρ := fun i : ℕ => if i ∈ a then some (σ i) else none
           IsKCNF 2 (φ.filterMap fun c =>
             if c.any (fun l => ρ l.1 == some l.2) then none
             else some (c.filter fun l => (ρ l.1).isNone))) ∧
          (2 ^ (digits + 1)) ^ a.card ≤ p.eval (encodeCNF φ).length) →
        encodeCNF φ ∈ L := by
  obtain ⟨dec, hd, hc⟩ := L030
  let R : Set (List Bool × List Bool) := {q | query digits q ∈ KSAT 2}
  let test : List Bool × List Bool → Bool := fun q => dec (query digits q)
  have htest : ∀ q, q ∈ R ↔ test q = true := fun q => hd (query digits q)
  have htime : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp (query_cpt digits) hc
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
    query_sound digits φ _ ((htest _).mpr ((hanswer _).mp h).2)
  refine ⟨L, ⟨answer, fun _ => Iff.rfl, htimeL⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp ((hanswer x).mp hx).1
    exact ⟨φ, rfl, hsound φ hx⟩
  · rintro φ hwidth ⟨a, σ, hσ, ha, hb⟩
    refine (hanswer _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, ?_⟩
    obtain ⟨b, hlen, hmem⟩ := complete_query digits φ hwidth a σ hσ ha
    have hpow : 2 ^ b.length ≤ p.eval (encodeCNF φ).length := by
      calc
        _ ≤ 2 ^ ((digits + 1) * a.card) := Nat.pow_le_pow_right (by decide) hlen
        _ = (2 ^ (digits + 1)) ^ a.card := by rw [pow_mul]
        _ ≤ _ := hb
    have hblen : b.length ≤ p.eval (encodeCNF φ).length := Nat.lt_two_pow_self.le.trans hpow
    have hlim : 2 ^ (b.length + 1) ≤ (Polynomial.C 2 * p).eval (encodeCNF φ).length := by
      rw [pow_succ, Nat.mul_comm]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.mul_le_mul_left _ hpow
    have hrank := (BoundedEnumeration.idx_bound b).trans hlim
    exact (htest _).mp (hfind (encodeCNF φ)
      ⟨b, ⟨hblen, hmem⟩, (Nat.le_add_right _ _).trans hrank⟩).2
