import PEqualNP.Outside.MeasuredUnitRound
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private abbrev Raw := List Bool

private def state (z p a l : Raw) : Raw := pairB z (pairB p (pairB a l))
private def cap (s : Raw) : Raw := (unpairB s).1
private def formula (s : Raw) : Raw := (unpairB (unpairB s).2).1
private def assumed (s : Raw) : Raw := (unpairB (unpairB (unpairB s).2).2).1
private def known (s : Raw) : Raw := (unpairB (unpairB (unpairB s).2).2).2

private theorem projections (z p a l : Raw) :
    cap (state z p a l) = z ∧ formula (state z p a l) = p ∧
    assumed (state z p a l) = a ∧ known (state z p a l) = l := by
  simp [cap,formula,assumed,known,state,unpairB_pairB]

private def step (scan : Raw × Raw → Raw) (s : Raw) : Raw :=
  state (cap s) (formula s) (assumed s) (tk (cap s) (assumed s ++ scan (known s,formula s)))

private theorem step_cpt {scan : Raw × Raw → Raw}
    (hs : ComputableInPolyTime encodePair (fun x : Raw => x) scan) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (step scan) := by
  have hz := cpt_unpairB1
  have hp := cpt_unpairB1_1 cpt_unpairB2
  have hr := cpt_unpairB2_1 cpt_unpairB2
  have ha := cpt_unpairB1_1 hr
  have hl := cpt_unpairB2_1 hr
  have h := cpt_comp (cpt_pair hl hp) hs
  exact cpt_pairB2 hz (cpt_pairB2 hp (cpt_pairB2 ha (cpt_tk hz (cpt_app2 ha h))))

private def measure (s : Raw) : ℕ := (cap s).length+3

private theorem step_measure (scan : Raw × Raw → Raw) (s : Raw) :
    measure (step scan s) ≤ measure s := by
  unfold step measure
  rw [(projections _ _ _ _).1]

private theorem step_length (scan : Raw × Raw → Raw) (s : Raw) :
    (step scan s).length ≤ s.length+measure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have ht := tk_length (cap s) (assumed s ++ scan (known s,formula s))
  simp only [step,state,measure,pairB_length]
  dsimp only [cap,formula,assumed,known] at ht ⊢
  omega

private theorem measure_bound (s : Raw) : measure s ≤ 3*s.length+3 := by
  have h := unpairB_length s
  unfold measure cap
  omega

private theorem flat_code_bound (φ : CNF) :
    ((φ.flatMap id).flatMap encodeLiteral).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [he]
      simp only [List.flatMap_cons,id_eq,List.flatMap_append,List.length_append,encodeClause,List.length_cons,List.length_nil]
      omega

private theorem neg_length (c : Clause) :
    ((c.map negLit).flatMap encodeLiteral).length = (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      simp only [List.map_cons,List.flatMap_cons,List.length_append,ih]
      simp only [encodeLiteral_eq,List.length_cons,negLit]

private theorem walk (scan : Raw × Raw → Raw)
    (hs : ∀ (φ : CNF) (L : List Literal), scan (L.flatMap encodeLiteral,encodeCNF φ) =
      (φ.flatMap (fun c => c.filter (canForce L c))).flatMap encodeLiteral)
    (z : Raw) (φ : CNF) (a : List Literal)
    (hcap : ((a ++ φ.flatMap id).flatMap encodeLiteral).length ≤ z.length) (n : ℕ) :
    (step scan)^[n] (state z (encodeCNF φ) (a.flatMap encodeLiteral) (a.flatMap encodeLiteral)) =
      state z (encodeCNF φ) (a.flatMap encodeLiteral) ((unitKnown φ a n).flatMap encodeLiteral) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      have hp := projections z (encodeCNF φ) (a.flatMap encodeLiteral) ((unitKnown φ a n).flatMap encodeLiteral)
      have hbound := ((unit_sublist φ a (n+1)).flatMap encodeLiteral).length_le.trans hcap
      simp only [step,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hs,tk_eq]
      rw [← List.flatMap_append]
      change state z (encodeCNF φ) (a.flatMap encodeLiteral)
        (((unitKnown φ a (n+1)).flatMap encodeLiteral).take z.length) = _
      rw [List.take_of_length_le hbound]

/-- An exact measured reverse unit propagation test on a canonically
encoded CNF and candidate clause, using the pinned finite-set definition. -/
theorem MeasuredRUP :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ : CNF) (c : Clause),
        test (encodeCNF φ,encodeClause c) = true ↔
          IsRUP {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ x ∈ φ, x.toFinset = d} c.toFinset := by
  obtain ⟨round,hr,hrs⟩ := MeasuredUnitRound
  obtain ⟨scan,hs,hss⟩ := MeasuredCNFFalsified
  have hneg : ComputableInPolyTime (fun w : Raw => w) (fun w : Raw => w) negI := cpt_negI cpt_id
  obtain ⟨negate,hn,hns⟩ := MeasuredLiteralMap (fun p => negI p.2) (cpt_comp cpt_snd hneg)
  let a := fun s => negate ([],(unpairB s).2)
  let init := fun s => state s (unpairB s).1 (a s) (a s)
  let out := fun s => (step round)^[s.length] (init s)
  let test := fun p : Raw × Raw => scan (known (out (pairB p.1 p.2)),p.1)
  have ha := cpt_comp (cpt_pair (cpt_const []) cpt_unpairB2) hn
  have hi := cpt_pairB2 cpt_id (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 ha ha))
  have hout := cpt_iterMeasure (step_cpt hr) measure 3 (step_measure round)
    (step_length round) measure_bound cpt_id hi
  have hl := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hout))
  have ht : ComputableInPolyTime encodePair Computability.encodeBool test :=
    cpt_comp (cpt_pairG (cpt_comp (g := fun s => known (out s)) cpt_pairB hl) cpt_fst) hs
  refine ⟨test,ht,fun φ c => ?_⟩
  let s := pairB (encodeCNF φ) (encodeClause c)
  let A := c.map negLit
  have htotal : ((A ++ φ.flatMap id).flatMap encodeLiteral).length ≤ s.length := by
    have hφ := flat_code_bound φ
    simp only [s,A,List.flatMap_append,List.length_append,neg_length,pairB_length]
    have hc : (c.flatMap encodeLiteral).length ≤ (encodeClause c).length := by
      simp [encodeClause]
    omega
  have hn : (A ++ φ.flatMap id).length ≤ s.length :=
    (length_le_flatMap_lit _).trans htotal
  have hac : a s = A.flatMap encodeLiteral := by
    simp only [a,s,unpairB_pairB,hns,negI_lit,A,List.flatMap_map,Function.comp_apply]
    rfl
  have he : out s =
      state s (encodeCNF φ) (A.flatMap encodeLiteral) ((unitKnown φ A s.length).flatMap encodeLiteral) := by
    have hscan (p : CNF) (L : List Literal) :
        round (L.flatMap encodeLiteral,encodeCNF p) = (p.flatMap (fun c => c.filter (canForce L c))).flatMap encodeLiteral :=
      hrs p L
    change (step round)^[s.length] (state s (unpairB s).1 (a s) (a s)) = _
    rw [hac,show (unpairB s).1 = encodeCNF φ by simp [s,unpairB_pairB]]
    exact walk round hscan s φ A htotal s.length
  change scan (known (out s),encodeCNF φ) = true ↔ IsRUP (clauseSet φ) c.toFinset
  rw [he,(projections _ _ _ _).2.2.2,hss]
  have hR := rup_iff φ c s.length hn
  simp only [falsified,List.any_eq_true,List.all_eq_true,decide_eq_true_eq] at hR
  exact hR

end PEqualNP.Outside
