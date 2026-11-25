import PEqualNP.Outside.MeasuredBoundedClauseUniverse
import PEqualNP.Outside.MeasuredResolutionRound
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private abbrev Raw := List Bool

private def state (u φ known trace : Raw) : Raw := pairB u (pairB φ (pairB known trace))
private def ambient (s : Raw) : Raw := (unpairB s).1
private def root (s : Raw) : Raw := (unpairB (unpairB s).2).1
private def known (s : Raw) : Raw := (unpairB (unpairB (unpairB s).2).2).1
private def found (s : Raw) : Raw := (unpairB (unpairB (unpairB s).2).2).2

private theorem projections (u p l t : Raw) :
    ambient (state u p l t) = u ∧ root (state u p l t) = p ∧
    known (state u p l t) = l ∧ found (state u p l t) = t := by
  simp [ambient,root,known,found,state,unpairB_pairB]

private def step (advance : Raw → Raw) (s : Raw) : Raw :=
  let next := tk (ambient s) (advance (pairB (root s) (pairB (ambient s) (known s))))
  state (ambient s) (root s) next (next ++ found s)

private theorem step_cpt {advance : Raw → Raw}
    (h : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) advance) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (step advance) := by
  have hu := cpt_unpairB1
  have hp := cpt_unpairB1_1 cpt_unpairB2
  have hr := cpt_unpairB2_1 cpt_unpairB2
  have hl := cpt_unpairB1_1 hr
  have ht := cpt_unpairB2_1 hr
  have hn := cpt_tk hu (cpt_comp (cpt_pairB2 hp (cpt_pairB2 hu hl)) h)
  exact cpt_pairB2 hu (cpt_pairB2 hp (cpt_pairB2 hn (cpt_app2 hn ht)))

private def measure (s : Raw) : ℕ := 3*(ambient s).length+3

private theorem step_measure (advance : Raw → Raw) (s : Raw) :
    measure (step advance s) ≤ measure s := by
  dsimp only [measure,step]
  rw [(projections _ _ _ _).1]

private theorem step_length (advance : Raw → Raw) (s : Raw) :
    (step advance s).length ≤ s.length+measure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hn := tk_length (ambient s) (advance (pairB (root s) (pairB (ambient s) (known s))))
  simp only [measure,step,state,pairB_length,List.length_append]
  dsimp only [ambient,root,known,found] at hn ⊢
  omega

private theorem measure_bound (s : Raw) : measure s ≤ 3*s.length+3 := by
  have h := unpairB_length s
  unfold measure ambient
  omega

private theorem round_size (φ U old : CNF) :
    (encodeCNF (resolutionRound φ U old)).length ≤ (encodeCNF U).length := by
  have h : (resolutionRound φ U old).Sublist U := by unfold resolutionRound; exact List.filter_sublist
  exact (h.flatMap encodeClause).length_le

private theorem walk (advance : Raw → Raw)
    (hs : ∀ φ U old : CNF, advance (pairB (encodeCNF φ) (pairB (encodeCNF U) (encodeCNF old))) =
      encodeCNF (resolutionRound φ U old))
    (φ U : CNF) (n : ℕ) :
    (step advance)^[n] (state (encodeCNF U) (encodeCNF φ) [] []) =
      state (encodeCNF U) (encodeCNF φ) (encodeCNF (resolutionKnown φ U n)) (encodeCNF (resolutionTrace φ U n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      let s := state (encodeCNF U) (encodeCNF φ) (encodeCNF (resolutionKnown φ U n)) (encodeCNF (resolutionTrace φ U n))
      have hproj : ambient s = encodeCNF U ∧ root s = encodeCNF φ ∧
          known s = encodeCNF (resolutionKnown φ U n) ∧ found s = encodeCNF (resolutionTrace φ U n) :=
        projections _ _ _ _
      have ht : tk (encodeCNF U) (encodeCNF (resolutionRound φ U (resolutionKnown φ U n))) =
          encodeCNF (resolutionRound φ U (resolutionKnown φ U n)) := by
        rw [tk_eq,List.take_of_length_le (round_size φ U _)]
      have happ (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by simp [encodeCNF]
      change step advance s = _
      simp only [step,hproj.1,hproj.2.1,hproj.2.2.1,hproj.2.2.2,hs,ht,known_step,resolutionTrace,happ]

private theorem count_bound (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [he,List.length_append,List.length_cons]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

theorem measuredResolutionSaturationOnPair :
    ∃ derive : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) derive ∧
      ∀ φ U : CNF, derive (encodeCNF φ,encodeCNF U) =
        encodeCNF (resolutionTrace φ U (encodeCNF U).length) := by
  obtain ⟨advance,ha,has⟩ := MeasuredResolutionRound
  let init := fun s => state (unpairB s).2 (unpairB s).1 [] []
  let iter := fun s => (step advance)^[(unpairB s).2.length] (init s)
  let run := fun s => found (iter s)
  have hi : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) init :=
    cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const (pairB [] [])))
  have hr := cpt_iterMeasure (step_cpt ha) measure 3 (step_measure advance) (step_length advance)
    measure_bound cpt_unpairB2 hi
  have hd : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) run :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hr))
  refine ⟨fun p => run (pairB p.1 p.2),cpt_comp (g := run) cpt_pairB hd,fun φ U => ?_⟩
  have hw : ∀ p U old : CNF, advance (pairB (encodeCNF p) (pairB (encodeCNF U) (encodeCNF old))) =
      encodeCNF (resolutionRound p U old) := has
  simp only [run,iter,init,unpairB_pairB,walk advance hw φ U,(projections _ _ _ _).2.2.2]

/-- For any fixed width, construct a valid canonical resolution derivation
whose empty-line condition exactly detects a refutation of that width. -/
theorem MeasuredResolutionSaturation (k : ℕ) :
    ∃ derive : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) derive ∧
      ∀ φ : CNF, ∃ ρ : CNF, derive (encodeCNF φ) = encodeCNF ρ ∧
        PEqualNP.ProofComplexity.IsDerivation
          {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) ∧
        (∀ d ∈ ρ.map List.toFinset, Finset.card d ≤ k) ∧
        ([] ∈ ρ ↔ ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
          ∀ d ∈ π, Finset.card d ≤ k) := by
  obtain ⟨gen,hgen,hgs⟩ := MeasuredBoundedClauseUniverse k
  obtain ⟨run,hr,hrs⟩ := measuredResolutionSaturationOnPair
  refine ⟨fun x => run (x,gen x),cpt_comp (cpt_pair cpt_id hgen) hr,fun φ => ?_⟩
  obtain ⟨U,he,hU⟩ := hgs φ
  let n := (encodeCNF U).length
  let ρ := resolutionTrace φ U n
  refine ⟨ρ,?_,resolutionTrace_derives φ U n,
    resolutionTrace_width φ U k n (fun c hc => ((hU c).mp hc).1),
    resolutionTrace_empty φ U k n hU (count_bound U)⟩
  change run (encodeCNF φ,gen (encodeCNF φ)) = _
  rw [he,hrs]

end PEqualNP.Outside
