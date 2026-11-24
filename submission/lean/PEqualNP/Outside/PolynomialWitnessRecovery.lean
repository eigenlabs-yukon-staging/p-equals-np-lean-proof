import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Verifier" => List Bool × List Bool → Bool

private def recoverStep (v : Verifier) (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let c := (unpairB (unpairB s).2).1
  let fl := (unpairB (unpairB s).2).2
  let reject := pairB x (pairB (succB c) [])
  let accept := pairB x (pairB c [true])
  sel fl (sel (bflag (v (x, c))) reject accept) s

private theorem recoverStep_length (v : Verifier) (s : List Bool) :
    (recoverStep v s).length ≤ s.length + 5 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  have hc := bf_succB_length (unpairB (unpairB s).2).1
  unfold recoverStep
  dsimp only
  apply sel_length
  · apply sel_length
    · rw [pairB_length, pairB_length]
      simp only [List.length_nil]
      omega
    · rw [pairB_length, pairB_length]
      simp only [List.length_cons, List.length_nil]
      omega
  · omega

private theorem recoverStep_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    CPT (recoverStep v) := by
  have hx := cpt_unpairB1
  have hr := cpt_unpairB2
  have hc := cpt_unpairB1_1 hr
  have hf := cpt_unpairB2_1 hr
  have hyes := cpt_pairB2 hx (cpt_pairB2 hc (cpt_const [true]))
  have hno := cpt_pairB2 hx (cpt_pairB2 (cpt_comp hc bf_cpt_succB) (cpt_const []))
  have ht := cpt_comp (cpt_pair hx hc) hv
  exact bf_cptl (cpt_sel hf (cpt_sel (cpt_bitFlag ht) hno hyes) cpt_id) (fun _ => rfl)

private def unpackResult (s : List Bool) : List Bool :=
  sel (unpairB (unpairB s).2).2 [] (true :: (unpairB (unpairB s).2).1)

private theorem unpackResult_polyTime : CPT unpackResult :=
  bf_cptl (cpt_sel (cpt_unpairB2_1 cpt_unpairB2) (cpt_const [])
    (cpt_cons1 true (cpt_unpairB1_1 cpt_unpairB2))) (fun _ => rfl)

private theorem recover_irreducible (v : Verifier) (x c : List Bool) :
    recoverStep v (pairB x (pairB c [true])) = pairB x (pairB c [true]) := by
  simp [recoverStep, unpairB_pairB]

private theorem recover_iter (v : Verifier) (x : List Bool) (n : Nat) :
    ∀ c : List Bool,
      let out := unpackResult ((recoverStep v)^[n] (pairB x (pairB c [])))
      (out = [] ∧ ∀ j < n, v (x, succB^[j] c) = false) ∨
        ∃ j < n, out = true :: succB^[j] c ∧ v (x, succB^[j] c) = true ∧
          ∀ i < j, v (x, succB^[i] c) = false := by
  induction n with
  | zero =>
    intro c
    left
    simp [unpackResult, unpairB_pairB]
  | succ n ih =>
    intro c
    dsimp only
    rw [Function.iterate_succ_apply]
    cases h : v (x, c) with
    | false =>
      have hstep : recoverStep v (pairB x (pairB c [])) = pairB x (pairB (succB c) []) := by
        simp [recoverStep, unpairB_pairB, bflag, h]
      rw [hstep]
      rcases ih (succB c) with ⟨hout, hfalse⟩ | ⟨j, hj, hout, htrue, hfirst⟩
      · left
        refine ⟨hout, ?_⟩
        intro j hj
        cases j with
        | zero => simpa using h
        | succ j =>
          rw [Function.iterate_succ_apply]
          exact hfalse j (by omega)
      · right
        refine ⟨j + 1, by omega, ?_, ?_, ?_⟩
        · rw [Function.iterate_succ_apply]; exact hout
        · rw [Function.iterate_succ_apply]; exact htrue
        · intro i hi
          cases i with
          | zero => simpa using h
          | succ i =>
            rw [Function.iterate_succ_apply]
            exact hfirst i (by omega)
    | true =>
      have hstep : recoverStep v (pairB x (pairB c [])) = pairB x (pairB c [true]) := by
        simp [recoverStep, unpairB_pairB, bflag, h]
      rw [hstep, Function.iterate_fixed (recover_irreducible v x c) n]
      right
      exact ⟨0, by omega, by simp [unpackResult, unpairB_pairB], by simpa using h,
        fun i hi => False.elim (by omega)⟩

private def recover (v : Verifier) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  unpackResult ((recoverStep v)^[p.eval x.length] (pairB x (pairB [] [])))

private theorem recover_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat) :
    CPT (recover v p) :=
  bf_cptl (cpt_comp (cpt_iterGrow (recoverStep_polyTime hv) 5 (recoverStep_length v) (L055 p)
    (cpt_pairB2 cpt_id (cpt_pairB2 (cpt_const []) (cpt_const [])))) unpackResult_polyTime)
    (fun x => by simp [recover])

/-- Recover an actual accepted witness within the same polynomial enumeration budget.
The empty output indicates failure; a leading true bit marks a returned witness. -/
theorem PolynomialWitnessRecovery (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (covers : ∀ x : List Bool, (∃ w : List Bool, (x, w) ∈ R) →
      ∃ w : List Bool, (x, w) ∈ R ∧ 2 ^ (w.length + 1) ≤ p.eval x.length + 1) :
    ∃ f : List Bool → List Bool, CPT f ∧
      ∀ x : List Bool,
        (f x = [] ∧ ∀ w : List Bool, (x, w) ∉ R) ∨
          ∃ w : List Bool, f x = true :: w ∧ (x, w) ∈ R := by
  obtain ⟨v, spec, hv⟩ := hR
  refine ⟨recover v p, recover_polyTime hv p, fun x => ?_⟩
  rcases recover_iter v x (p.eval x.length) [] with ⟨hout, hfalse⟩ | ⟨j, _, hout, htrue, _⟩
  · left
    refine ⟨hout, fun w hw => ?_⟩
    obtain ⟨w', hw', hlen⟩ := covers x ⟨w, hw⟩
    have hidx := idx_bound w'
    have hcheck := hfalse (idx w') (by omega)
    change v (x, cand (idx w')) = false at hcheck
    rw [cand_idx, (spec (x, w')).mp hw'] at hcheck
    contradiction
  · exact Or.inr ⟨cand j, hout, (spec (x, cand j)).mpr htrue⟩

/-- Run the same search with a candidate count supplied as a unary-size word. -/
def unaryRecovery (v : Verifier) (p : List Bool × List Bool) : List Bool :=
  unpackResult ((recoverStep v)^[p.2.length] (pairB p.1 (pairB [] [])))

theorem unaryRecovery_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair (fun x => x) (unaryRecovery v) := by
  have hinit := cpt_pairB2 cpt_unpairB1 (cpt_const (pairB [] []))
  have hr := cpt_iterGrow (recoverStep_polyTime hv) 5 (recoverStep_length v)
    cpt_unpairB2 hinit
  have h := cpt_comp cpt_pairB (cpt_comp hr unpackResult_polyTime)
  apply bf_cptl h
  rintro ⟨x, b⟩
  simp [unaryRecovery, unpairB_pairB]

theorem unaryRecovery_spec (v : Verifier) (x b : List Bool) :
    (unaryRecovery v (x,b) = [] ∧ ∀ j < b.length, v (x, cand j) = false) ∨
      ∃ j < b.length, unaryRecovery v (x,b) = true :: cand j ∧ v (x, cand j) = true ∧
        ∀ i < j, v (x, cand i) = false :=
  recover_iter v x b.length []

end PEqualNP.Outside
