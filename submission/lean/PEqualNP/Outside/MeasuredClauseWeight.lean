import PEqualNP.Outside.ClauseWeightCarry
import PEqualNP.Outside.MeasuredWidthClassCount
import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def bin (φ : CNF) (width : ℕ) : ℕ := (φ.filter (fun c => c.length = width)).length

private def step (count : List Bool × List Bool → List Bool) (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let cap := (unpairB (unpairB s).2).1
  let rest := (unpairB (unpairB s).2).2
  let width := (unpairB rest).1.tail
  let acc := (unpairB rest).2
  pairB x (pairB cap (pairB width (tk cap (count (width,x) ++ half acc))))

private def measure (s : List Bool) : ℕ := (unpairB (unpairB s).2).1.length + 3

private theorem step_cpt {count : List Bool × List Bool → List Bool}
    (h : ComputableInPolyTime encodePair (fun x : List Bool => x) count) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step count) := by
  have hx := cpt_unpairB1
  have hp := cpt_unpairB1_1 cpt_unpairB2
  have hr := cpt_unpairB2_1 cpt_unpairB2
  have hw := cpt_tail1 (cpt_unpairB1_1 hr)
  have ha := cpt_comp (cpt_unpairB2_1 hr) cpt_half'
  have hn := cpt_comp (cpt_pair hw hx) h
  exact cpt_pairB2 hx (cpt_pairB2 hp (cpt_pairB2 hw (cpt_tk hp (cpt_app2 hn ha))))

private theorem measure_step (count : List Bool × List Bool → List Bool) (s : List Bool) :
    measure (step count s) ≤ measure s := by
  simp [measure,step,unpairB_pairB]

private theorem step_length (count : List Bool × List Bool → List Bool) (s : List Bool) :
    (step count s).length ≤ s.length + measure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  let r := (unpairB (unpairB s).2).2
  have htail : (unpairB r).1.tail.length ≤ (unpairB r).1.length := by simp
  have hcap := tk_length (unpairB (unpairB s).2).1
    (count ((unpairB r).1.tail,(unpairB s).1) ++ half (unpairB r).2)
  dsimp only [r] at htail hcap
  simp only [measure,step,pairB_length]
  omega

private theorem measure_bound (s : List Bool) : measure s ≤ 3*s.length+3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  simp only [measure]
  omega

private theorem run {count : List Bool × List Bool → List Bool}
    (hs : ∀ width : List Bool, ∀ φ : CNF,
      count (width,encodeCNF φ) = List.replicate (bin φ width.length) true)
    (φ : CNF) (cap width : List Bool) (acc : ℕ)
    (hc : acc+width.length*φ.length ≤ cap.length) :
    (unpairB (unpairB (unpairB ((step count)^[width.length]
      (pairB (encodeCNF φ) (pairB cap (pairB width (List.replicate acc true)))))).2).2).2 =
      List.replicate ((List.range width.length).foldr (fun k a => bin φ k+a/2) acc) true := by
  induction width generalizing acc with
  | nil => simp [unpairB_pairB]
  | cons b width ih =>
      have hb : bin φ width.length ≤ φ.length := List.length_filter_le _ _
      have ha : acc/2 ≤ acc := Nat.div_le_self _ _
      have hlen : bin φ width.length + acc/2 + width.length*φ.length ≤ cap.length := by
        rw [List.length_cons,Nat.succ_mul] at hc
        omega
      have ht : (List.replicate (bin φ width.length) true ++ List.replicate (acc/2) true).length ≤ cap.length := by
        simp only [List.length_append,List.length_replicate]
        omega
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [step,unpairB_pairB,List.tail_cons,hs,half_eq,List.length_replicate,un]
      rw [tk_eq,List.take_of_length_le ht,List.replicate_append_replicate,ih _ hlen]
      rw [List.range_succ,List.foldr_append]
      rfl

private theorem width_le_code (φ : CNF) (c : Clause) (hc : c ∈ φ) :
    c.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp at hc
  | cons d φ ih =>
      have hcode : encodeCNF (d :: φ) = encodeClause d ++ encodeCNF φ := by simp [encodeCNF]
      rw [hcode,List.length_append]
      rcases List.mem_cons.mp hc with rfl | hc
      · apply (PEqualNP.Library.SearchHelpers.SatV.length_le_flatMap_lit c).trans
        simp only [encodeClause,List.length_append]
        omega
      · exact (ih hc).trans (Nat.le_add_left _ _)

private theorem count_le_code (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [List.length_cons,he,List.length_append]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

/-- The dyadic clause-weight threshold is decidable by a measured unary carry loop. -/
theorem MeasuredClauseWeight :
    ∃ test : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool test ∧
      ∀ φ : CNF,
        test (encodeCNF φ) = true ↔ (φ.map (fun c => (2 : ℚ)⁻¹ ^ c.length)).sum < 1 := by
  obtain ⟨count,hc,hs⟩ := MeasuredWidthClassCount
  let width := fun x : List Bool => true :: x
  let cap := fun x => mulU (width x) (width x)
  let initial := fun x => pairB x (pairB (cap x) (pairB (width x) []))
  let output := fun x => (unpairB (unpairB (unpairB ((step count)^[(width x).length] (initial x))).2).2).2
  have hw := cpt_cons1 true cpt_id
  have hi := cpt_pairB2 cpt_id (cpt_pairB2 (cpt_mulU2 hw hw) (cpt_pairB2 hw (cpt_const [])))
  have hloop := cpt_iterMeasure (step_cpt hc) measure 3 (measure_step count) (step_length count) measure_bound hw hi
  have ho : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) output :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hloop))
  let test := fun x => (output x).isEmpty
  have ht := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_sel ho (cpt_const [true]) (cpt_const [])) bf_cpt_neL
  have he : (fun x => !(sel (output x) [true] []).isEmpty) = test := by
    funext x
    unfold test
    cases output x <;> rfl
  rw [he] at ht
  refine ⟨test,ht,fun φ => ?_⟩
  let x := encodeCNF φ
  have hcap : 0+(width x).length*φ.length ≤ (cap x).length := by
    have hl : φ.length ≤ (width x).length := by
      have := count_le_code φ
      simp only [width,List.length_cons,x]
      omega
    simp only [cap,mulU,un,List.length_replicate,Nat.zero_add]
    exact Nat.mul_le_mul_left _ hl
  have hs' (w : List Bool) (ψ : CNF) :
      count (w,encodeCNF ψ) = List.replicate (bin ψ w.length) true := hs w ψ
  change (output x).isEmpty = true ↔ _
  dsimp only [output,initial]
  have hrun := run hs' φ (cap x) (width x) 0 hcap
  change (unpairB (unpairB (unpairB ((step count)^[(width x).length]
    (pairB x (pairB (cap x) (pairB (width x) []))))).2).2).2 = _ at hrun
  rw [hrun]
  simp only [List.isEmpty_iff,List.replicate_eq_nil_iff]
  simpa only [List.foldr_map,bin,width,List.length_cons,Nat.succ_eq_add_one] using ClauseWeightCarry φ x.length (fun c hc => width_le_code φ c hc)

end PEqualNP.Outside
