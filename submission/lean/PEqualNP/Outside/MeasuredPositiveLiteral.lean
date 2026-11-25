import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def positiveFront (s : List Bool) : Bool := s.headD false && s.tail.headD false

private theorem cpt_positive {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bflag (positiveFront (f s))) := by
  have h := cpt_sel (cpt_hd1 hf) (cpt_const [])
    (cpt_sel (cpt_hd1 (cpt_tail1 hf)) (cpt_const []) (cpt_const [true]))
  refine cptE h (fun s => ?_)
  rcases f s with _ | ⟨b,_ | ⟨t,rest⟩⟩
  · rfl
  · cases b <;> rfl
  · cases b <;> cases t <;> rfl

private def step (s : List Bool) : List Bool := if positiveFront s then s else dropI s

private theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
  refine cptE (cpt_sel (cpt_positive cpt_id) cpt_dropI cpt_id) (fun s => ?_)
  unfold step
  cases positiveFront s <;> rfl

private theorem step_length (s : List Bool) : (step s).length ≤ s.length := by
  unfold step
  split
  · exact le_rfl
  · exact dropI_length s

private def output (s : List Bool) : List Bool :=
  if positiveFront s then (headI s).tail.tail else []

private theorem output_cpt {f : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => output (f s)) := by
  refine cptE (cpt_sel (cpt_positive hf) (cpt_const [])
    (cpt_tail1 (cpt_tail1 (cpt_comp hf cpt_headI)))) (fun s => ?_)
  unfold output
  cases positiveFront (f s) <;> rfl

private theorem fixed (s : List Bool) (h : step s = s) (n : ℕ) : step^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,h,ih]

private theorem clause_cons (l : Literal) (c : Clause) :
    encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]

private theorem front_lit (l : Literal) (c : Clause) :
    positiveFront (encodeClause (l :: c)) = l.2 := by
  rw [clause_cons,encodeLiteral_eq]
  simp [positiveFront]

private theorem run (c : Clause) (n : ℕ) (hn : c.length ≤ n) :
    output (step^[n] (encodeClause c)) =
      ((c.filter fun l => l.2).head?).elim [] (fun l => vcode l.1) := by
  induction c generalizing n with
  | nil =>
      have h : step (encodeClause []) = [] := by rfl
      cases n with
      | zero => rfl
      | succ n =>
          rw [Function.iterate_succ_apply,h,fixed [] (by rfl)]
          rfl
  | cons l c ih =>
      cases l with
      | mk i b =>
          cases b with
          | true =>
              have he : step (encodeClause ((i,true) :: c)) = encodeClause ((i,true) :: c) := by
                simp [step,front_lit]
              rw [fixed _ he n]
              rw [output,front_lit,ite_eq_left rfl,clause_cons,headI_lit]
              rfl
          | false =>
              cases n with
              | zero => simp at hn
              | succ n =>
                  have ht : c.length ≤ n := by simpa using hn
                  have he : step (encodeClause ((i,false) :: c)) = encodeClause c := by
                    rw [step,front_lit,clause_cons,dropI_lit]
                    rfl
                  rw [Function.iterate_succ_apply,he,ih n ht]
                  rfl

private theorem clause_length (c : Clause) : c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      rw [clause_cons,List.length_append,List.length_cons]
      have := vcode_length_pos l.1
      simp only [encodeLiteral_eq,List.length_cons]
      omega

/-- Find the first positive variable of an encoded clause, returning its original
binary variable code and the empty word when none exists. -/
theorem MeasuredPositiveLiteral :
    ∃ first : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) first ∧
      ∀ c : Clause, first (encodeClause c) =
        ((c.filter fun l => l.2).head?).elim []
          (fun l => (l.1.bits.flatMap fun b => [true,b]) ++ [false,true]) := by
  let first := fun s => output (step^[s.length] s)
  have hi := cpt_iterLen cpt_step step_length cpt_id cpt_id
  refine ⟨first,output_cpt hi,fun c => ?_⟩
  exact run c _ (clause_length c)

end PEqualNP.Outside
