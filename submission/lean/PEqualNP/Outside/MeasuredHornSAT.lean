import PEqualNP.Outside.MeasuredHornSweep
import PEqualNP.Library.SearchHelpers.TwoSatStr
import PEqualNP.Library.SearchHelpers.SatVerifierCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def codes (vs : List ℕ) : List Bool := vs.flatMap vcode

private def step (sweep : List Bool × List Bool → List Bool) (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let cap := (unpairB (unpairB s).2).1
  let witness := (unpairB (unpairB s).2).2
  pairB x (pairB cap (tk cap (sweep (x,witness))))

private def measure (s : List Bool) : ℕ := (unpairB (unpairB s).2).1.length + 2

private theorem step_cpt {sweep : List Bool × List Bool → List Bool}
    (h : ComputableInPolyTime encodePair (fun x : List Bool => x) sweep) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step sweep) := by
  have hx := cpt_unpairB1
  have hp := cpt_unpairB1_1 cpt_unpairB2
  have hw := cpt_unpairB2_1 cpt_unpairB2
  exact cpt_pairB2 hx (cpt_pairB2 hp (cpt_tk hp (cpt_comp (cpt_pair hx hw) h)))

private theorem measure_step (sweep : List Bool × List Bool → List Bool) (s : List Bool) :
    measure (step sweep s) ≤ measure s := by
  simp [measure,step,unpairB_pairB]

private theorem step_length (sweep : List Bool × List Bool → List Bool) (s : List Bool) :
    (step sweep s).length ≤ s.length + measure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := tk_length (unpairB (unpairB s).2).1
    (sweep ((unpairB s).1,(unpairB (unpairB s).2).2))
  simp only [step,measure,pairB_length]
  omega

private theorem measure_bound (s : List Bool) : measure s ≤ 2*s.length+2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  simp only [measure]
  omega

private theorem vars_bound (φ : CNF) : (formulaVars φ).card ≤ (encodeCNF φ).length := by
  unfold formulaVars
  have h := List.toFinset_card_le ((φ.flatMap id).map Prod.fst)
  have hsize := PEqualNP.Library.SearchHelpers.TwoSat.size_le φ
  simp only [List.length_map] at h
  omega

private theorem run {sweep : List Bool × List Bool → List Bool}
    (hs : ∀ (φ : CNF) (vs : List ℕ), ∃ ys : List ℕ,
        sweep (encodeCNF φ,codes vs) = codes ys ∧
        ys.toFinset = hornSweep φ vs.toFinset ∧
        (codes ys).length ≤ (codes vs).length + (encodeCNF φ).length)
    (φ : CNF) (cap : List Bool) (n : ℕ) (hn : n*(encodeCNF φ).length ≤ cap.length) :
    ∃ vs : List ℕ,
      (step sweep)^[n] (pairB (encodeCNF φ) (pairB cap [])) =
        pairB (encodeCNF φ) (pairB cap (codes vs)) ∧
      vs.toFinset = (hornSweep φ)^[n] ∅ ∧
      (codes vs).length ≤ n*(encodeCNF φ).length := by
  induction n with
  | zero => exact ⟨[],rfl,rfl,by simp [codes]⟩
  | succ n ih =>
      have hn' : n*(encodeCNF φ).length ≤ cap.length := by
        rw [Nat.succ_mul] at hn
        omega
      obtain ⟨vs,hst,hset,hlen⟩ := ih hn'
      obtain ⟨ys,hy,hYset,hYlen⟩ := hs φ vs
      have hBound : (codes ys).length ≤ (n+1)*(encodeCNF φ).length := by
        rw [Nat.succ_mul]
        omega
      refine ⟨ys,?_,?_,hBound⟩
      · rw [Function.iterate_succ_apply', hst]
        simp only [step,unpairB_pairB,hy]
        rw [tk_eq,List.take_of_length_le (hBound.trans hn)]
      · rw [Function.iterate_succ_apply']
        exact hYset.trans (congrArg (hornSweep φ) hset)

private theorem asg_eq (vs : List ℕ) : asg (codes vs) = hornAssignment vs.toFinset := by
  funext i
  rw [Bool.eq_iff_iff, codes, asg_codes]
  simp [hornAssignment]

/-- A deterministic polynomial-time machine agrees with satisfiability on all canonical
Horn formulae, using the unmodified reference CNF encoding. -/
theorem MeasuredHornSAT :
    ∃ D : Language Bool, D ∈ P ∧ ∀ φ : CNF,
      (∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) →
      (encodeCNF φ ∈ D ↔ Satisfiable φ) := by
  obtain ⟨sweep,hs,hsem⟩ := measuredHornSweep_semantics
  let cap := fun x : List Bool => mulU x x
  let initial := fun x => pairB x (pairB (cap x) [])
  let w := fun x : List Bool => (unpairB (unpairB ((step sweep)^[x.length] (initial x))).2).2
  have hinit := cpt_pairB2 cpt_id (cpt_pairB2 (cpt_mulU2 cpt_id cpt_id) (cpt_const []))
  have hit := cpt_iterMeasure (step_cpt hs) measure 2 (measure_step sweep)
    (step_length sweep) measure_bound cpt_id hinit
  have hw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) w :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hit)
  let d := fun x => SV (x,w x)
  let D : Language Bool := {x | d x = true}
  have hD : D ∈ P := ⟨d,fun _ => Iff.rfl,cpt_comp (cpt_pair cpt_id hw) cpt_SV⟩
  refine ⟨D,hD,fun φ hHorn => ?_⟩
  let x := encodeCNF φ
  have hcap : x.length*x.length ≤ (cap x).length := by simp [cap,mulU,un]
  obtain ⟨vs,hst,hset,_⟩ := run hsem φ (cap x) x.length hcap
  have hw' : w x = codes vs := by
    dsimp only [w,initial]
    rw [hst]
    simp only [unpairB_pairB]
  change SV (encodeCNF φ,w x) = true ↔ Satisfiable φ
  rw [hw',SV_iff,asg_eq,hset]
  have hsat := horn_sweep_decides φ hHorn x.length (vars_bound φ)
  rw [hsat]
  constructor
  · rintro ⟨F,hF,he⟩
    exact (PEqualNP.Library.SearchHelpers.encodeCNF_injective hF) ▸ he
  · intro he
    exact ⟨φ,rfl,he⟩

end PEqualNP.Outside
