import PEqualNP.Outside.TwoSatBackdoorInP

namespace PEqualNP.Outside.ExtractedBackdoor

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV

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


theorem solve (p : Polynomial ℕ) (extract : CNF → List ℕ) (encoded : List Bool → List Bool)
    (henc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) encoded)
    (hspec_enc : ∀ φ : CNF, encoded (encodeCNF φ) = (extract φ).flatMap vcode)
    (hwidth : ∀ φ : CNF, ∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ extract φ))).length ≤ 2) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF, 2 ^ (extract φ).length ≤ p.eval (encodeCNF φ).length →
        (encodeCNF φ ∈ L ↔ Satisfiable φ) := by
  obtain ⟨B, ⟨dec, hd, htime⟩, hspec⟩ := TwoSatBackdoorInP p
  let input (x : List Bool) := pairB x (encoded x)
  let answer (x : List Bool) := !(sel (bflag (wfB x)) [] (bflag (dec (input x)))).isEmpty
  let L : Language Bool := {x | answer x = true}
  have hinput : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) input :=
    cpt_pairB2 cpt_id henc
  have hanswer : ∀ x, x ∈ L ↔ wfB x = true ∧ input x ∈ B := by
    intro x
    change answer x = true ↔ wfB x = true ∧ input x ∈ B
    calc
      answer x = true ↔ wfB x = true ∧ dec (input x) = true := by
        cases h : wfB x <;> cases h' : dec (input x) <;> simp [answer, h, h', sel, bflag]
      _ ↔ wfB x = true ∧ input x ∈ B := and_congr_right fun _ => (hd (input x)).symm
  have hinput_enc (φ : CNF) :
      input (encodeCNF φ) = pairB (encodeCNF φ) ((extract φ).flatMap vcode) := by
    simp only [input, hspec_enc]
  have hP : L ∈ P := by
    refine ⟨answer, fun _ => Iff.rfl, ?_⟩
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const []) (cpt_bitFlag (cpt_comp hinput htime)))
      cpt_nonempty
    exact h
  have hsound (φ : CNF) (h : encodeCNF φ ∈ L) : Satisfiable φ := by
    have hB := (hanswer _).mp h |>.2
    rw [hinput_enc] at hB
    exact (hspec φ (extract φ)).1 hB
  refine ⟨L, hP, ?_, ?_⟩
  · intro x hx
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp ((hanswer _).mp hx).1
    exact ⟨φ, rfl, hsound φ hx⟩
  · intro φ hbudget
    refine ⟨hsound φ, fun h => (hanswer _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, ?_⟩⟩
    rw [hinput_enc]
    apply (hspec φ (extract φ)).2 (hwidth φ) ?_ h
    have hle : (encodeCNF φ).length ≤
        (pairB (encodeCNF φ) ((extract φ).flatMap vcode)).length := by
      rw [pairB_length]
      omega
    exact hbudget.trans (PrefixDecideHelpers.eval_mono_nat p hle)

end PEqualNP.Outside.ExtractedBackdoor
