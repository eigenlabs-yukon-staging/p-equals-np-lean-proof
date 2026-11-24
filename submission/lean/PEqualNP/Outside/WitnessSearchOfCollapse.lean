import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Verifier" => List Bool × List Bool → Bool

private def extension (v : Verifier) : Language Bool :=
  {s | ∃ t : List Bool, v ((unpairB s).1, (unpairB s).2 ++ t) = true}

private theorem extension_np {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat)
    (bound : ∀ x w : List Bool, v (x, w) = true → w.length ≤ p.eval x.length) :
    extension v ∈ NP := by
  let f := fun s : List Bool => (unpairB s).1
  let g := fun s : List Bool => (unpairB s).2
  let R : Set (List Bool × List Bool) := {q | v (f q.1, g q.1 ++ q.2) = true}
  have appendPrefix : ComputableInPolyTime encodePair encodePair
      (fun q : List Bool × List Bool => (f q.1, g q.1 ++ q.2)) := by
    have left : CPT f := cpt_unpairB1
    have right : CPT g := cpt_unpairB2
    have h₁ := cpt_comp cpt_unpairB1 left
    have h₂ := cpt_comp (cpt_pair (cpt_comp cpt_unpairB1 right) cpt_unpairB2) cpt_append
    have h := cpt_comp cpt_pairB (cpt_pair h₁ h₂)
    simpa [f, g, unpairB_pairB] using h
  refine ⟨R, p, ⟨fun q => v (f q.1, g q.1 ++ q.2), fun _ => Iff.rfl,
    cpt_comp appendPrefix hv⟩, fun s => ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_, ht⟩
    have h := bound _ _ ht
    have hs := unpairB_length s
    exact (by rw [List.length_append] at h; omega : t.length ≤ p.eval (unpairB s).1.length) |>.trans
      (eval_mono p (by omega))
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩

private def extendStep (v : Verifier) (d : List Bool → Bool) (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let w := (unpairB s).2
  let s₀ := pairB x (w ++ [false])
  let s₁ := pairB x (w ++ [true])
  sel (bflag (v (x, w))) (sel (bflag (d s₁)) s₀ s₁) s

private theorem extendStep_length (v : Verifier) (d : List Bool → Bool) (s : List Bool) :
    (extendStep v d s).length ≤ s.length + 2 := by
  have hs := unpairB_length s
  unfold extendStep
  dsimp only
  apply sel_length
  · apply sel_length <;> rw [pairB_length, List.length_append] <;> simp <;> omega
  · omega

private theorem extendStep_polyTime {v : Verifier} {d : List Bool → Bool}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (hd : ComputableInPolyTime (fun x => x) Computability.encodeBool d) :
    CPT (extendStep v d) := by
  have hx := cpt_unpairB1
  have hw := cpt_unpairB2
  have h₀ := cpt_pairB2 hx (cpt_app2 hw (cpt_const [false]))
  have h₁ := cpt_pairB2 hx (cpt_app2 hw (cpt_const [true]))
  have ha := cpt_bitFlag (cpt_comp cpt_unpairB hv)
  have he := cpt_bitFlag (cpt_comp h₁ hd)
  exact bf_cptl (cpt_sel ha (cpt_sel he h₀ h₁) cpt_id) (fun _ => rfl)

private theorem extend_exists {v : Verifier} {d : List Bool → Bool}
    (hd : ∀ s : List Bool, s ∈ extension v ↔ d s = true)
    (x w : List Bool) (he : ∃ t : List Bool, v (x, w ++ t) = true) :
    ∃ w' : List Bool,
      extendStep v d (pairB x w) = pairB x w' ∧
      (∃ t : List Bool, v (x, w' ++ t) = true) ∧
      (v (x, w') = true ∨ w'.length = w.length + 1) := by
  cases h : v (x, w) with
  | true =>
    exact ⟨w, by simp [extendStep, unpairB_pairB, bflag, h], he, Or.inl h⟩
  | false =>
    cases ht : d (pairB x (w ++ [true])) with
    | true =>
      have hmem := (hd _).mpr ht
      refine ⟨w ++ [true], by simp [extendStep, unpairB_pairB, bflag, h, ht],
        ?_, Or.inr (by simp)⟩
      change (∃ t, v ((unpairB _).1, (unpairB _).2 ++ t) = true) at hmem
      simpa [unpairB_pairB] using hmem
    | false =>
      refine ⟨w ++ [false], by simp [extendStep, unpairB_pairB, bflag, h, ht],
        ?_, Or.inr (by simp)⟩
      obtain ⟨t, ht'⟩ := he
      cases t with
      | nil => simp [h] at ht'
      | cons b t =>
        cases b
        · exact ⟨t, by simpa [List.append_assoc] using ht'⟩
        · have hmem : pairB x (w ++ [true]) ∈ extension v := by
            change ∃ z, v ((unpairB _).1, (unpairB _).2 ++ z) = true
            exact ⟨t, by simpa [unpairB_pairB, List.append_assoc] using ht'⟩
          rw [(hd _).mp hmem] at ht
          contradiction

private theorem extend_iter {v : Verifier} {d : List Bool → Bool}
    (hd : ∀ s : List Bool, s ∈ extension v ↔ d s = true)
    (x : List Bool) (he : ∃ t : List Bool, v (x, t) = true) (n : Nat) :
    ∃ w : List Bool,
      (extendStep v d)^[n] (pairB x []) = pairB x w ∧
      (∃ t : List Bool, v (x, w ++ t) = true) ∧
      (v (x, w) = true ∨ w.length = n) := by
  induction n with
  | zero => exact ⟨[], rfl, by simpa using he, Or.inr rfl⟩
  | succ n ih =>
    obtain ⟨w, hstate, hw, haccept⟩ := ih
    rw [Function.iterate_succ_apply', hstate]
    rcases haccept with h | hlen
    · exact ⟨w, by simp [extendStep, unpairB_pairB, bflag, h], hw, Or.inl h⟩
    · obtain ⟨w', hstep, hw', h' | h'⟩ := extend_exists hd x w hw
      · exact ⟨w', hstep, hw', Or.inl h'⟩
      · exact ⟨w', hstep, hw', Or.inr (h'.trans (by omega))⟩

private def verifyResult (v : Verifier) (s : List Bool) : List Bool :=
  sel (bflag (v (unpairB s))) [] (true :: (unpairB s).2)

private theorem verifyResult_polyTime {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    CPT (verifyResult v) :=
  bf_cptl (cpt_sel (cpt_bitFlag (cpt_comp cpt_unpairB hv)) (cpt_const [])
    (cpt_cons1 true cpt_unpairB2)) (fun _ => rfl)

/-- From collapse, obtain polynomial-time witness production for every reference verifier
whose accepted witnesses satisfy a fixed polynomial length bound. -/
theorem WitnessSearchOfCollapse (collapse : NP ⊆ P)
    (R : Set (List Bool × List Bool)) (hR : DecidableInPolyTime encodePair R)
    (p : Polynomial Nat)
    (bound : ∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) :
    ∃ f : List Bool → List Bool, CPT f ∧
      ∀ x : List Bool,
        (f x = [] ∧ ∀ w : List Bool, (x, w) ∉ R) ∨
          ∃ w : List Bool, f x = true :: w ∧ (x, w) ∈ R := by
  obtain ⟨v, hvSpec, hv⟩ := hR
  have hb (x w : List Bool) (h : v (x, w) = true) : w.length ≤ p.eval x.length :=
    bound x w ((hvSpec (x,w)).mpr h)
  have hP : extension v ∈ P := collapse (extension_np hv p hb)
  obtain ⟨d, hdSpec, hd⟩ := hP
  let run := fun x : List Bool =>
    (extendStep v d)^[p.eval x.length] (pairB x [])
  have hrun : CPT run :=
    bf_cptl (cpt_iterGrow (extendStep_polyTime hv hd) 2 (extendStep_length v d)
      (L055 p) (cpt_pairB2 cpt_id (cpt_const []))) (fun x => by simp [run])
  refine ⟨fun x => verifyResult v (run x), cpt_comp hrun (verifyResult_polyTime hv), fun x => ?_⟩
  by_cases he : ∃ t : List Bool, v (x, t) = true
  · obtain ⟨w, hstate, hw, h | hlen⟩ := extend_iter hdSpec x he (p.eval x.length)
    · exact Or.inr ⟨w, by simp [run, hstate, verifyResult, unpairB_pairB, bflag, h],
        (hvSpec (x,w)).mpr h⟩
    · obtain ⟨t, ht⟩ := hw
      have hs := hb x (w ++ t) ht
      have hempty : t = [] := List.length_eq_zero_iff.mp (by rw [List.length_append] at hs; omega)
      have h : v (x, w) = true := by simpa [hempty] using ht
      exact Or.inr ⟨w, by simp [run, hstate, verifyResult, unpairB_pairB, bflag, h],
        (hvSpec (x,w)).mpr h⟩
  · have hf (w : List Bool) : v (x, w) = false := by
      cases h : v (x, w)
      · rfl
      · exact False.elim (he ⟨w, h⟩)
    have hi : ∀ n : Nat, ∃ w : List Bool,
        (extendStep v d)^[n] (pairB x []) = pairB x w := by
      intro n
      induction n with
      | zero => exact ⟨[], rfl⟩
      | succ n ih =>
        obtain ⟨w, hw⟩ := ih
        rw [Function.iterate_succ_apply', hw]
        cases hh : d (pairB x (w ++ [true]))
        · exact ⟨w ++ [false], by simp [extendStep, unpairB_pairB, hf, bflag, hh]⟩
        · exact ⟨w ++ [true], by simp [extendStep, unpairB_pairB, hf, bflag, hh]⟩
    obtain ⟨w, hw⟩ := hi (p.eval x.length)
    exact Or.inl ⟨by simp [run, hw, verifyResult, unpairB_pairB, bflag, hf],
      fun t ht => he ⟨t, (hvSpec (x,t)).mp ht⟩⟩

end PEqualNP.Outside
