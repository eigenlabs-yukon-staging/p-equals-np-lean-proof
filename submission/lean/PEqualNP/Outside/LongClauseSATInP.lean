import PEqualNP.Outside.LongClauseNames
import PEqualNP.Outside.UniqueNameScan
import PEqualNP.Outside.TwoSatBackdoorInP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.LongClauseCollector (gather gather_cpt)
open PEqualNP.Outside.LongClauseNames (longNames gather_enc)
open PEqualNP.Outside.UniqueNameScan (unique unique_cpt unique_enc scan scan_count mem_scan)

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

private theorem long_width (φ : CNF) :
    ∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ scan [] (longNames φ)))).length ≤ 2 := by
  intro c hc
  by_cases h : 2 < c.length
  · have hn : c.filter (fun l => decide (l.1 ∉ scan [] (longNames φ))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro l hl
      have hmem : l.1 ∈ longNames φ := by
        apply List.mem_flatMap.mpr
        exact ⟨c, hc, by simp [h, List.mem_map.mpr ⟨l, hl, rfl⟩]⟩
      have hm := (mem_scan l.1 [] (longNames φ)).mpr (Or.inr hmem)
      simp [hm]
    rw [hn]
    simp
  · exact (List.length_filter_le _ _).trans (by omega)

theorem PEqualNP.Outside.LongClauseSATInP (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF,
        2 ^ (φ.flatMap (fun c => if 2 < c.length then c.map Prod.fst else [])).toFinset.card ≤
          p.eval (encodeCNF φ).length →
        (encodeCNF φ ∈ L ↔ Satisfiable φ) := by
  obtain ⟨B, ⟨dec, hd, htime⟩, hspec⟩ := TwoSatBackdoorInP p
  let input (x : List Bool) := pairB x (unique (gather x))
  let answer (x : List Bool) := !(sel (bflag (wfB x)) [] (bflag (dec (input x)))).isEmpty
  let L : Language Bool := {x | answer x = true}
  have hinput : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) input :=
    cpt_pairB2 cpt_id (cpt_comp gather_cpt unique_cpt)
  have hanswer : ∀ x, x ∈ L ↔ wfB x = true ∧ input x ∈ B := by
    intro x
    change answer x = true ↔ wfB x = true ∧ input x ∈ B
    calc
      answer x = true ↔ wfB x = true ∧ dec (input x) = true := by
        cases h : wfB x <;> cases h' : dec (input x) <;> simp [answer, h, h', sel, bflag]
      _ ↔ wfB x = true ∧ input x ∈ B := and_congr_right fun _ => (hd (input x)).symm
  have hinput_enc (φ : CNF) :
      input (encodeCNF φ) = pairB (encodeCNF φ) ((scan [] (longNames φ)).flatMap vcode) := by
    simp only [input, gather_enc, unique_enc]
  have hP : L ∈ P := by
    refine ⟨answer, fun _ => Iff.rfl, ?_⟩
    have h := cpt_comp (cpt_sel wfFlag_cpt (cpt_const []) (cpt_bitFlag (cpt_comp hinput htime)))
      cpt_nonempty
    exact h
  have hsound (φ : CNF) (h : encodeCNF φ ∈ L) : Satisfiable φ := by
    have hB := (hanswer _).mp h |>.2
    rw [hinput_enc] at hB
    exact (hspec φ (scan [] (longNames φ))).1 hB
  refine ⟨L, hP, ?_, ?_⟩
  · intro x hx
    obtain ⟨φ, rfl⟩ := (wfB_iff x).mp ((hanswer _).mp hx).1
    exact ⟨φ, rfl, hsound φ hx⟩
  · intro φ hbudget
    refine ⟨hsound φ, fun h => (hanswer _).mpr ⟨(wfB_iff _).mpr ⟨φ, rfl⟩, ?_⟩⟩
    rw [hinput_enc]
    apply (hspec φ (scan [] (longNames φ))).2 (long_width φ) ?_ h
    have hle : (encodeCNF φ).length ≤
        (pairB (encodeCNF φ) ((scan [] (longNames φ)).flatMap vcode)).length := by
      rw [pairB_length]
      omega
    rw [scan_count]
    exact hbudget.trans (PrefixDecideHelpers.eval_mono_nat p hle)
