import PEqualNP.Outside.RenamableHornPairConstraints
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search

private def item (l : Option Literal) : List Bool := l.elim [false,false] encodeLiteral

private def items (φ : CNF) : List (Option Literal) := φ.flatMap (fun c => c.map some ++ [none])

private theorem item_codes (φ : CNF) : (items φ).flatMap item = encodeCNF φ := by
  simp only [items,encodeCNF,List.flatMap_assoc,List.flatMap_append,List.flatMap_map,item]
  apply List.flatMap_congr
  intro c _
  simp [encodeClause,item]

private theorem items_len (ls : List (Option Literal)) : ls.length ≤ (ls.flatMap item).length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      have hl : 1 ≤ (item l).length := by cases l <;> simp [item,encodeLiteral]
      omega

private def changeItem (w it : List Bool) : List Bool :=
  if it.headD false then if memB it.tail.tail w then negI it else it else it

private def step (s : List Bool) : List Bool :=
  let w := (unpairB s).1
  let r := (unpairB (unpairB s).2).1
  let out := (unpairB (unpairB s).2).2
  pairB w (pairB (dropI r) (out ++ tk (headI r) (changeItem w (headI r))))

private theorem step_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
  have hw := cpt_unpairB1
  have hr := cpt_unpairB1_1 cpt_unpairB2
  have ho := cpt_unpairB2_1 cpt_unpairB2
  have hi := cpt_comp hr cpt_headI
  have hf := cpt_memB (cpt_tail1 (cpt_tail1 hi)) hw
  have hm := cpt_sel (cpt_hd1 hi) hi (cpt_sel hf hi (cpt_negI hi))
  have hm' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => changeItem (unpairB s).1 (headI (unpairB (unpairB s).2).1)) := by
    refine cptE hm (fun s => ?_)
    unfold changeItem
    let r := headI (unpairB (unpairB s).2).1
    change sel (hd r) r (sel (bflag (memB r.tail.tail (unpairB s).1)) r (negI r)) =
      (if r.headD false then if memB r.tail.tail (unpairB s).1 then negI r else r else r)
    cases r with
    | nil => rfl
    | cons b r =>
        cases b with
        | false => rfl
        | true =>
            cases memB (true :: r).tail.tail (unpairB s).1 <;> rfl
  exact cpt_pairB2 hw (cpt_pairB2 (cpt_comp hr cpt_dropI) (cpt_app2 ho (cpt_tk hi hm')))

private theorem step_length (s : List Bool) : (step s).length ≤ s.length+2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  let r := (unpairB (unpairB s).2).1
  have h3 := congrArg List.length (headI_dropI r)
  have ht := tk_length (headI r) (changeItem (unpairB s).1 (headI r))
  simp only [List.length_append] at h3
  dsimp only [r] at h3 ht
  simp only [step,pairB_length,List.length_append]
  omega

private theorem change_literal (w : List Bool) (l : Literal) :
    changeItem w (encodeLiteral l) = encodeLiteral (flipLiteral (asg w) l) := by
  have hh : (encodeLiteral l).headD false = true := rfl
  have ht : (encodeLiteral l).tail.tail = vcode l.1 := by rw [encodeLiteral_eq]; rfl
  rw [changeItem,hh,ite_eq_left rfl,ht]
  cases h : asg w l.1
  · have hm : memB (vcode l.1) w = false := h
    simp [hm,flipLiteral,h]
  · have hm : memB (vcode l.1) w = true := h
    simp only [hm,ite_true,negI_lit,flipLiteral,h]
    obtain ⟨i,b⟩ := l
    cases b <;> rfl

private def renamed (w : List Bool) (l : Option Literal) : List Bool :=
  l.elim [false,false] (fun l => encodeLiteral (flipLiteral (asg w) l))

private theorem renamed_len (w : List Bool) (l : Option Literal) :
    (renamed w l).length = (item l).length := by
  cases l with
  | none => rfl
  | some l => simp [renamed,item,encodeLiteral,flipLiteral]

private theorem renamed_codes (w : List Bool) (φ : CNF) :
    (items φ).flatMap (renamed w) = encodeCNF (flipFormula (asg w) φ) := by
  simp only [items,flipFormula,encodeCNF,List.flatMap_assoc,List.flatMap_append,List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  simp [renamed,encodeClause,List.flatMap_map]

private theorem run (w : List Bool) (ls : List (Option Literal)) (out : List Bool)
    (n : ℕ) (hn : ls.length ≤ n) :
    step^[n] (pairB w (pairB (ls.flatMap item) out)) =
      pairB w (pairB [] (out ++ ls.flatMap (renamed w))) := by
  induction n generalizing ls out with
  | zero =>
      have hnil : ls = [] := List.length_eq_zero_iff.mp (by omega)
      subst ls
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases ls with
      | nil =>
          have hstep : step (pairB w (pairB ([] : List Bool) out)) = pairB w (pairB [] out) := by
            simp [step,unpairB_pairB,dropI,headI,tk_eq]
          simp only [List.flatMap_nil]
          rw [hstep]
          exact ih [] out (by simp)
      | cons l ls =>
          have ht : ls.length ≤ n := by simpa using hn
          have hstep : step (pairB w (pairB ((l :: ls).flatMap item) out)) =
              pairB w (pairB (ls.flatMap item) (out ++ renamed w l)) := by
            cases l with
            | none =>
                simp only [step,List.flatMap_cons,item,Option.elim_none,unpairB_pairB]
                rfl
            | some a =>
                simp only [step,List.flatMap_cons,item,Option.elim_some,unpairB_pairB,
                  headI_lit,dropI_lit,change_literal,tk_eq]
                have hlen := renamed_len w (some a)
                change (encodeLiteral (flipLiteral (asg w) a)).length = (encodeLiteral a).length at hlen
                rw [List.take_of_length_le (by omega)]
                rfl
          rw [hstep,ih _ _ ht,List.flatMap_cons,List.append_assoc]

theorem measuredCNFRenaming_semantics :
    ∃ applyFlip : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) applyFlip ∧
      ∀ (φ : CNF) (w : List Bool),
        applyFlip (encodeCNF φ,w) = encodeCNF (flipFormula (asg w) φ) := by
  let initial := fun s => pairB (unpairB s).2 (pairB (unpairB s).1 [])
  let loop := fun s => step^[(unpairB s).1.length] (initial s)
  let get := fun s => (unpairB (unpairB (loop s)).2).2
  have hi := cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const []))
  have hl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) loop :=
    cpt_iterGrow step_cpt 2 step_length cpt_unpairB1 hi
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) get :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hl)
  refine ⟨fun z => get (pairB z.1 z.2),cpt_comp (g := get) cpt_pairB hg,fun φ w => ?_⟩
  simp only [get,loop,initial,unpairB_pairB]
  have hsize : (items φ).length ≤ (encodeCNF φ).length := by
    rw [← item_codes]
    exact items_len _
  have hrun := run w (items φ) [] (encodeCNF φ).length hsize
  rw [item_codes,renamed_codes,List.nil_append] at hrun
  rw [hrun,unpairB_pairB,unpairB_pairB]

/-- Apply a sparse list of sign flips to a canonical reference CNF in polynomial time. -/
theorem MeasuredCNFRenaming :
    ∃ applyFlip : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) applyFlip ∧
      ∀ (φ : CNF) (vs : List ℕ),
        applyFlip (encodeCNF φ,vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true])) =
          encodeCNF (φ.map (fun c => c.map (fun l => (l.1,xor l.2 (decide (l.1 ∈ vs)))))) := by
  obtain ⟨f,hf,hs⟩ := measuredCNFRenaming_semantics
  refine ⟨f,hf,fun φ vs => ?_⟩
  change f (encodeCNF φ,vs.flatMap vcode) =
    encodeCNF (flipFormula (fun i => decide (i ∈ vs)) φ)
  rw [hs]
  have he : asg (vs.flatMap vcode) = fun i => decide (i ∈ vs) := by
    funext i
    rw [Bool.eq_iff_iff,asg_codes]
    simp
  rw [he]

end PEqualNP.Outside
