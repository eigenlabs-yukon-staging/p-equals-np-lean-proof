import PEqualNP.Outside.HornClosureCompleteness
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Outside.MeasuredPositiveLiteral
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

private def advance (c : Clause) (vs : List ℕ) : List ℕ :=
  if c.eval (hornAssignment vs.toFinset) then vs
  else ((c.filter fun l => l.2).head?).elim vs (fun l => vs ++ [l.1])

private def sweepList (φ : CNF) (vs : List ℕ) : List ℕ :=
  φ.foldl (fun vs c => advance c vs) vs

private theorem asg_eq (vs : List ℕ) : asg (codes vs) = hornAssignment vs.toFinset := by
  funext i
  rw [Bool.eq_iff_iff, codes, asg_codes]
  simp [hornAssignment]

private theorem clause_check (c : Clause) (vs : List ℕ) :
    SV (encodeClause c,codes vs) = c.eval (hornAssignment vs.toFinset) := by
  rw [Bool.eq_iff_iff]
  have he : encodeCNF [c] = encodeClause c := by simp [encodeCNF]
  rw [SV_iff]
  constructor
  · rintro ⟨φ,hφ,heval⟩
    have h := PEqualNP.Library.SearchHelpers.encodeCNF_injective (hφ.trans he.symm)
    subst φ
    simpa [CNF.eval,asg_eq] using heval
  · intro hv
    exact ⟨[c],he,by simpa [CNF.eval,asg_eq] using hv⟩

private theorem step_set (c : Clause) (vs : List ℕ) :
    (advance c vs).toFinset = hornStep c vs.toFinset := by
  unfold advance hornStep
  split
  · rfl
  · cases (c.filter fun l => l.2).head? <;> simp

private theorem sweep_set (φ : CNF) (vs : List ℕ) :
    (sweepList φ vs).toFinset = hornSweep φ vs.toFinset := by
  induction φ generalizing vs with
  | nil => rfl
  | cons c φ ih =>
      change (sweepList φ (advance c vs)).toFinset = hornSweep φ (hornStep c vs.toFinset)
      rw [ih,step_set]

private theorem positive_code_le (c : Clause) :
    (((c.filter fun l => l.2).head?).elim [] (fun l => vcode l.1)).length ≤ (encodeClause c).length := by
  cases h : (c.filter fun l => l.2).head? with
  | none => simp
  | some l =>
      have hmem : l ∈ c := by
        obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.mp h
        have hf : l ∈ c.filter (fun l => l.2) := by rw [ht]; exact List.mem_cons_self
        exact (List.mem_filter.mp hf).1
      have hval (xs : Clause) (hm : l ∈ xs) : (vcode l.1).length ≤ (encodeClause xs).length := by
        induction xs with
        | nil => simp at hm
        | cons a xs ih =>
            have he : encodeClause (a :: xs) = encodeLiteral a ++ encodeClause xs := by
              simp [encodeClause]
            rw [he,List.length_append]
            rcases List.mem_cons.mp hm with heq | ht
            · rw [← heq,encodeLiteral_eq]
              simp only [List.length_cons]
              omega
            · exact (ih ht).trans (Nat.le_add_left _ _)
      simpa only [Option.elim_some] using hval c hmem

private theorem advance_codes (c : Clause) (vs : List ℕ) :
    codes (advance c vs) =
      if c.eval (hornAssignment vs.toFinset) then codes vs
      else codes vs ++ (((c.filter fun l => l.2).head?).elim [] (fun l => vcode l.1)) := by
  unfold advance
  split
  · rfl
  · cases (c.filter fun l => l.2).head? <;> simp [codes,List.flatMap_append]

private theorem sweep_size (φ : CNF) (vs : List ℕ) :
    (codes (sweepList φ vs)).length ≤ (codes vs).length + (encodeCNF φ).length := by
  induction φ generalizing vs with
  | nil => simp [sweepList,encodeCNF]
  | cons c φ ih =>
      have hrec := ih (advance c vs)
      have hstep : (codes (advance c vs)).length ≤ (codes vs).length + (encodeClause c).length := by
        rw [advance_codes]
        split
        · omega
        · have := positive_code_le c
          rw [List.length_append]
          omega
      change (codes (sweepList φ (advance c vs))).length ≤ _
      have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [he,List.length_append]
      omega

private def step (split : List Bool → List Bool × List Bool) (first : List Bool → List Bool)
    (s : List Bool) : List Bool :=
  let remaining := (unpairB s).1
  let w := (unpairB s).2
  let c := (split remaining).1
  if remaining = [] then s
  else pairB (split remaining).2 (if SV (c,w) then w else w ++ tk c (first c))

private theorem step_cpt
    {split : List Bool → List Bool × List Bool} {first : List Bool → List Bool}
    (hs : ComputableInPolyTime (fun x : List Bool => x) encodePair split)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) first) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step split first) := by
  have hr := cpt_unpairB1
  have hw := cpt_unpairB2
  have hh := cpt_comp hr hs
  have hc := cpt_comp hh cpt_fst
  have ht := cpt_comp hh cpt_snd
  have check := cpt_bitFlag (cpt_comp (cpt_pair hc hw) cpt_SV)
  have he := cpt_tk hc (cpt_comp hc hf)
  have hnew := cpt_sel check (cpt_app2 hw he) hw
  refine cptE (cpt_sel hr cpt_id (cpt_pairB2 ht hnew)) (fun s => ?_)
  simp only [sel,step]
  split
  · rfl
  · cases SV ((split (unpairB s).1).1,(unpairB s).2) <;> rfl

private theorem step_length {split : List Bool → List Bool × List Bool} {first : List Bool → List Bool}
    (hj : ∀ s, (split s).1 ++ (split s).2 = s) (s : List Bool) :
    (step split first s).length ≤ s.length + 1 := by
  have h1 := unpairB_length s
  have h2 := congrArg List.length (hj (unpairB s).1)
  have ht := tk_length (split (unpairB s).1).1 (first (split (unpairB s).1).1)
  simp only [List.length_append] at h2
  dsimp only [step]
  split
  · omega
  · rw [pairB_length]
    split
    · omega
    · rw [List.length_append]
      omega

private theorem step_canonical
    {split : List Bool → List Bool × List Bool} {first : List Bool → List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hf : ∀ c, first (encodeClause c) =
      ((c.filter fun l => l.2).head?).elim [] (fun l => vcode l.1))
    (c : Clause) (r : List Bool) (vs : List ℕ) :
    step split first (pairB (encodeClause c ++ r) (codes vs)) =
      pairB r (codes (advance c vs)) := by
  have he : encodeClause c ++ r ≠ [] := by simp [encodeClause]
  simp only [step,unpairB_pairB,hs,ite_eq_right he,clause_check,advance_codes,hf]
  rw [tk_eq,List.take_of_length_le (positive_code_le c)]

private theorem run
    {split : List Bool → List Bool × List Bool} {first : List Bool → List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hf : ∀ c, first (encodeClause c) =
      ((c.filter fun l => l.2).head?).elim [] (fun l => vcode l.1))
    (φ : CNF) (vs : List ℕ) (n : ℕ) (hn : φ.length ≤ n) :
    (step split first)^[n] (pairB (encodeCNF φ) (codes vs)) = pairB [] (codes (sweepList φ vs)) := by
  induction n generalizing φ vs with
  | zero =>
      have e : φ = [] := List.length_eq_zero_iff.mp (by omega)
      subst φ
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have e : step split first (pairB (encodeCNF []) (codes vs)) =
              pairB (encodeCNF []) (codes vs) := by simp [step,encodeCNF,unpairB_pairB]
          rw [e,ih [] _ (by simp)]
      | cons c φ =>
          have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
          rw [he,step_canonical hs hf,ih φ _ (by simpa using hn)]
          rfl

private theorem clause_count (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      change φ.length+1 ≤ (encodeClause c ++ encodeCNF φ).length
      simp only [encodeClause,List.length_append,List.length_cons,List.length_nil]
      omega

theorem measuredHornSweep_semantics :
    ∃ sweep : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) sweep ∧
      ∀ (φ : CNF) (vs : List ℕ), ∃ ys : List ℕ,
        sweep (encodeCNF φ,vs.flatMap vcode) = ys.flatMap vcode ∧
        ys.toFinset = hornSweep φ vs.toFinset ∧
        (ys.flatMap vcode).length ≤ (vs.flatMap vcode).length + (encodeCNF φ).length := by
  obtain ⟨split,hs,hjoin,hspec⟩ := measuredFirstClause_reassembles
  obtain ⟨first,hf,hfspec⟩ := MeasuredPositiveLiteral
  let loop := fun s => (step split first)^[(unpairB s).1.length] s
  let sweep := fun p : List Bool × List Bool => (unpairB (loop (pairB p.1 p.2))).2
  have hl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) loop :=
    cpt_iterGrow (step_cpt hs hf) 1 (step_length hjoin) cpt_unpairB1 cpt_id
  have hc : ComputableInPolyTime encodePair (fun x : List Bool => x) sweep :=
    cpt_comp (g := fun s => (unpairB (loop s)).2) cpt_pairB (cpt_unpairB2_1 hl)
  refine ⟨sweep,hc,fun φ vs => ⟨sweepList φ vs,?_,sweep_set φ vs,sweep_size φ vs⟩⟩
  simp only [sweep,loop,unpairB_pairB]
  change (unpairB ((step split first)^[(encodeCNF φ).length]
    (pairB (encodeCNF φ) (codes vs)))).2 = codes (sweepList φ vs)
  rw [run hspec hfspec _ _ _ (clause_count φ),unpairB_pairB]

/-- A measured pass over a CNF adds selected positive-variable codes with linear output growth. -/
theorem MeasuredHornSweep :
    ∃ sweep : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) sweep ∧
      ∀ (φ : CNF) (vs : List ℕ), ∃ ys : List ℕ,
        sweep (encodeCNF φ,vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true])) =
          ys.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
        (ys.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true])).length ≤
          (vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true])).length +
            (encodeCNF φ).length := by
  obtain ⟨sweep,hc,hsem⟩ := measuredHornSweep_semantics
  refine ⟨sweep,hc,fun φ vs => ?_⟩
  obtain ⟨ys,ha,_,hb⟩ := hsem φ vs
  exact ⟨ys,ha,hb⟩

end PEqualNP.Outside
