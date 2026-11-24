import PEqualNP.Outside.OccurrenceNumbering
import PEqualNP.Outside.MeasuredClauseSplit
import PEqualNP.Outside.RecordPairScan

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Outside.CNFWidth (sign_cpt dropI_lt encodeLiteral_nonempty encodeCNF_append_local)
open PEqualNP.Library.SearchHelpers.S2D (incB bits_succ incB_length cpt_incB dig cpt_dig)
open PEqualNP.Outside.RecordPairScan (wire)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def literalBits (pol : Bool) (n : Word) : Word := [true,pol] ++ dig n ++ [false,true]

theorem literalBits_cpt (pol : Bool) : CPT (literalBits pol) :=
  cptl (cpt_app2 (cpt_app2 (cpt_const [true,pol]) cpt_dig) (cpt_const [false,true]))
    (fun _ => rfl)

theorem literalBits_enc (pol : Bool) (n : ℕ) :
    literalBits pol n.bits = encodeLiteral (n,pol) := rfl

theorem literalBits_len (pol : Bool) (n : Word) : (literalBits pol n).length = 2*n.length+4 := by
  simp [literalBits,dig]
  omega

def opsPack (r i m o : Word) : Word := pairB r (pairB i (pairB m o))
def input (s : Word) := (unpairB s).1
def counter (s : Word) := (unpairB (unpairB s).2).1
def mainOut (s : Word) := (unpairB (unpairB (unpairB s).2).2).1
def records (s : Word) := (unpairB (unpairB (unpairB s).2).2).2

def numberStep (s : Word) : Word :=
  let r := input s
  let i := counter s
  let m := mainOut s
  let o := records s
  let l := headI r
  sel r s (sel (bflag (isEnd r))
    (opsPack (dropI r) (incB i) (m ++ literalBits (polB l) i)
      (o ++ pairB (pairB l.tail.tail i) []))
    (opsPack (dropI r) i (m ++ [false,false]) o))

theorem numberStep_cpt : CPT numberStep := by
  have hR : CPT input := cpt_unpairB1
  have hI : CPT counter := cpt_unpairB1_1 cpt_unpairB2
  have h2 := cpt_unpairB2_1 cpt_unpairB2
  have hM : CPT mainOut := cpt_unpairB1_1 h2
  have hO : CPT records := cpt_unpairB2_1 h2
  have hdrop := cpt_comp hR cpt_dropI
  have hitem := cpt_comp hR cpt_headI
  have hcode : CPT (fun s => literalBits (polB (headI (input s))) (counter s)) :=
    cptl (cpt_sel (cpt_comp hitem sign_cpt) (cpt_comp hI (literalBits_cpt false))
      (cpt_comp hI (literalBits_cpt true))) (fun s => by cases polB (headI (input s)) <;> rfl)
  have hnew := cpt_pairB2 (cpt_pairB2 (cpt_tail1 (cpt_tail1 hitem)) hI) (cpt_const [])
  have hlit := cpt_pairB2 hdrop (cpt_pairB2 (cpt_comp hI cpt_incB)
    (cpt_pairB2 (cpt_app2 hM hcode) (cpt_app2 hO hnew)))
  have hclose := cpt_pairB2 hdrop (cpt_pairB2 hI (cpt_pairB2 (cpt_app2 hM (cpt_const [false,false])) hO))
  exact cptl (cpt_sel hR cpt_id (cpt_sel (cpt_comp hR cpt_isEndF) hlit hclose)) (fun _ => rfl)

def numberMeasure (s : Word) := 24*((input s).length+(counter s).length)+24

theorem numberState_bound (s : Word) :
    2*(input s).length + 2*(counter s).length + 2*(mainOut s).length + (records s).length ≤ s.length := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  dsimp [input,counter,mainOut,records]
  omega

theorem numberMeasure_step (s : Word) : numberMeasure (numberStep s) ≤ numberMeasure s := by
  by_cases hn : input s = []
  · simp [numberStep,sel,hn]
  · have hd := dropI_lt hn
    have hi := incB_length (counter s)
    rw [numberStep,sel,ite_eq_right hn]
    rw [sel]
    split <;> simp only [numberMeasure,opsPack,input,counter,unpairB_pairB] at * <;> omega

theorem numberStep_growth (s : Word) : (numberStep s).length ≤ s.length+numberMeasure s := by
  by_cases hn : input s = []
  · simp [numberStep,sel,hn]
  · have hd := dropI_lt hn
    have hi := incB_length (counter s)
    have ha := numberState_bound s
    have he := congrArg List.length (headI_dropI (input s))
    have htail : (headI (input s)).tail.tail.length ≤ (input s).length := by
      simp only [List.length_append] at he
      simp only [List.length_tail]
      omega
    rw [numberStep,sel,ite_eq_right hn]
    rw [sel]
    split <;> simp only [opsPack,pairB_length,literalBits_len,List.length_append,
      List.length_cons,List.length_nil,numberMeasure] <;> omega

def numberRun (s : Word) : Word := numberStep^[s.length] (opsPack s [] [] [])

theorem numberRun_cpt : CPT numberRun := by
  obtain ⟨m⟩ := numberStep_cpt
  have hi := Iter.iter_polyTime_measure numberStep m numberMeasure 24
    numberMeasure_step numberStep_growth (fun s => by have h := numberState_bound s; unfold numberMeasure; omega)
  have hp : CPT (fun s => opsPack s [] [] []) :=
    cpt_pairB2 cpt_id (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_const [])))
  exact cptl (cpt_comp (cpt_pair hp cpt_id) hi) (fun _ => rfl)


def items (j : ℕ) : Clause → List Word
  | [] => []
  | l :: ls => pairB (vcode l.1) j.bits :: items (j+1) ls

theorem items_append (j : ℕ) (a b : Clause) :
    items j (a++b) = items j a ++ items (j+a.length) b := by
  induction a generalizing j with
  | nil => simp [items]
  | cons l a ih =>
    simp only [List.cons_append,items,List.length_cons,ih]
    rw [show j+1+a.length = j+(a.length+1) by omega]

theorem wire_append_local (a b : List Word) : wire (a++b) = wire a ++ wire b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [wire,pairB,ih,List.append_assoc]

theorem numberStep_lit (j : ℕ) (l : Literal) (r m o : Word) :
    numberStep (opsPack (encodeLiteral l ++ r) j.bits m o) =
      opsPack r (j+1).bits (m ++ encodeLiteral (j,l.2)) (o ++ wire (items j [l])) := by
  have hnon : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral]
  have hpol : polB (encodeLiteral l) = l.2 := by cases l; rfl
  have htail : (encodeLiteral l).tail.tail = vcode l.1 := by cases l; rfl
  simp only [numberStep,opsPack,input,counter,mainOut,records,unpairB_pairB,
    sel,ite_eq_right hnon,isEnd_lit,bflag,List.nil_eq,List.isEmpty_nil,
    headI_lit,dropI_lit,hpol,htail,← bits_succ,literalBits_enc,items,wire]
  rfl

theorem numberStep_close (j : ℕ) (r m o : Word) :
    numberStep (opsPack (false :: false :: r) j.bits m o) =
      opsPack r j.bits (m ++ [false,false]) o := by
  simp [numberStep,opsPack,input,counter,mainOut,records,unpairB_pairB,sel,isEnd,bflag,dropI]

theorem numberStep_halt (j : ℕ) (m o : Word) :
    numberStep (opsPack [] j.bits m o) = opsPack [] j.bits m o := by
  simp [numberStep,opsPack,input,unpairB_pairB,sel]

theorem consume_literals (j : ℕ) (cl : Clause) (r m o : Word) :
    numberStep^[cl.length] (opsPack (cl.flatMap encodeLiteral ++ r) j.bits m o) =
      opsPack r (j+cl.length).bits (m ++ (number j cl).flatMap encodeLiteral) (o ++ wire (items j cl)) := by
  induction cl generalizing j m o with
  | nil => simp [number,items,wire]
  | cons l ls ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,Function.iterate_succ_apply]
    rw [numberStep_lit,ih]
    simp only [number,List.flatMap_cons,List.append_assoc,items,wire]
    rw [show (j+1)+ls.length = j+(ls.length+1) by omega]
    congr 2
    simp [pairB,List.append_assoc]

def tokens (F : CNF) : ℕ := F.flatten.length + F.length

theorem tokens_cons (cl : Clause) (F : CNF) :
    tokens (cl::F) = tokens F + (cl.length+1) := by
  simp only [tokens,List.flatten_cons,List.length_append,List.length_cons]
  omega

theorem consume_formula (j : ℕ) (F : CNF) (m o : Word) :
    numberStep^[tokens F] (opsPack (encodeCNF F) j.bits m o) =
      opsPack [] (j+F.flatten.length).bits (m ++ encodeCNF (main j F)) (o ++ wire (items j F.flatten)) := by
  induction F generalizing j m o with
  | nil => simp [tokens,encodeCNF,main,items,wire]
  | cons cl F ih =>
    rw [tokens_cons,Function.iterate_add_apply,Function.iterate_succ_apply']
    change numberStep^[tokens F]
      (numberStep (numberStep^[cl.length] (opsPack
        (encodeClause cl ++ encodeCNF F) j.bits m o))) = _
    have enc : encodeClause cl ++ encodeCNF F =
        cl.flatMap encodeLiteral ++ ((false :: false :: []) ++ encodeCNF F) := by
      simp [encodeClause,List.append_assoc]
    rw [enc,consume_literals]
    change numberStep^[tokens F] (numberStep (opsPack
      (false :: false :: encodeCNF F) (j+cl.length).bits _ _)) = _
    rw [numberStep_close,ih]
    simp only [main,encodeCNF,List.flatMap_cons,encodeClause,List.flatten_cons,List.length_append,
      items_append,wire_append_local,List.append_assoc,Nat.add_assoc]

theorem tokens_le (F : CNF) : tokens F ≤ (encodeCNF F).length := by
  have hc : ∀ cl : Clause, cl.length + 1 ≤ (encodeClause cl).length := by
    intro cl
    induction cl with
    | nil => simp [encodeClause]
    | cons l ls ih =>
      simp only [encodeClause,List.flatMap_cons,List.length_cons,List.length_append,List.length_nil] at *
      have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega
  induction F with
  | nil => simp [tokens,encodeCNF]
  | cons cl F ih =>
    rw [tokens_cons]
    have hh := hc cl
    simp only [encodeCNF,List.flatMap_cons,List.length_append] at *
    omega

theorem numberRun_enc (F : CNF) :
    numberRun (encodeCNF F) = opsPack [] F.flatten.length.bits
      (encodeCNF (main 0 F)) (wire (items 0 F.flatten)) := by
  have hk := tokens_le F
  unfold numberRun
  rw [← Nat.sub_add_cancel hk, Function.iterate_add_apply]
  change numberStep^[((encodeCNF F).length - tokens F)]
    (numberStep^[tokens F] (opsPack (encodeCNF F) (0:ℕ).bits [] [])) = _
  rw [consume_formula,Function.iterate_fixed (numberStep_halt ..)]
  simp only [Nat.zero_add,List.nil_append]

end PEqualNP.Outside.OccurrenceSplit
