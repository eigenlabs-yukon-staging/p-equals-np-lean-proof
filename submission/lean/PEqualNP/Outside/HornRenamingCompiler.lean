import PEqualNP.Outside.HornRenamingFacts
import PEqualNP.Outside.BackdoorPathCore
import PEqualNP.Outside.FirstWideCollector

namespace PEqualNP.Outside.HornRenamingCompiler

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_cpt cut_eq)
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Outside.FirstWideCollector (pack pack_length)
open PEqualNP.Outside.HornRenamingFacts (pairClauses pairCNF)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def original (z : Word) : Word := (unpairB z).1
def outer (z : Word) : Word := (unpairB (unpairB z).2).1
def inner (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def output (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2

def step (z : Word) : Word :=
  let x := original z
  let o := outer z
  let i := inner z
  let acc := output z
  let tail := dropI o
  let advance := pack x tail (cut x (dropI tail)) acc
  let more := (cut x (headI o) ++ cut x (headI i)) ++ [false, false]
  let emit := pack x o (dropI i) (acc ++ more)
  sel o z (sel (bflag (isEnd o)) (sel i advance (sel (bflag (isEnd i)) emit advance)) advance)

theorem step_cpt : CPT step := by
  have hx : CPT original := cpt_unpairB1
  have ho : CPT outer := cpt_unpairB1_1 cpt_unpairB2
  have q := cpt_unpairB2_1 cpt_unpairB2
  have hi : CPT inner := cpt_unpairB1_1 q
  have hacc : CPT output := cpt_unpairB2_1 q
  have ht := cpt_comp ho cpt_dropI
  have hadv := cpt_pairB2 hx (cpt_pairB2 ht (cpt_pairB2 (cut_cpt hx (cpt_comp ht cpt_dropI)) hacc))
  have hpair := cpt_app2 (cpt_app2 (cut_cpt hx (cpt_comp ho cpt_headI))
    (cut_cpt hx (cpt_comp hi cpt_headI))) (cpt_const [false, false])
  have hemit := cpt_pairB2 hx (cpt_pairB2 ho
    (cpt_pairB2 (cpt_comp hi cpt_dropI) (cpt_app2 hacc hpair)))
  exact cptl (cpt_sel ho cpt_id (cpt_sel (cpt_comp ho cpt_isEndF)
    (cpt_sel hi hadv (cpt_sel (cpt_comp hi cpt_isEndF) hemit hadv)) hadv)) (fun _ => rfl)

def measure (z : Word) : ℕ := 2 * (original z).length + 5

theorem original_step (z : Word) : original (step z) = original z := by
  simp only [step, sel]
  split
  · rfl
  · split
    · split
      · simp [original, pack, unpairB_pairB]
      · split <;> simp [original, pack, unpairB_pairB]
    · simp [original, pack, unpairB_pairB]

theorem head_length (x o : Word) : (cut x (headI o)).length ≤ x.length := by
  simp [cut_eq, List.length_take]

theorem step_length (z : Word) : (step z).length ≤ z.length + measure z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  have ho := dropI_length (outer z)
  have hi := dropI_length (inner z)
  have hoo : (cut (original z) (dropI (dropI (outer z)))).length ≤ (original z).length := by
    simp [cut_eq, List.length_take]
  have hl := head_length (original z) (outer z)
  have hr := head_length (original z) (inner z)
  have hadv : (pack (original z) (dropI (outer z)) (cut (original z) (dropI (dropI (outer z)))) (output z)).length ≤
      z.length + measure z := by
    -- The outer scan drops its current item before starting an inner row.
    -- At an advance, the old inner word may be short, so charge a bounded reset below.
    simp only [pack_length, measure, original, outer, inner, output] at *
    omega
  have hemit : (pack (original z) (outer z) (dropI (inner z)) (output z ++
      ((cut (original z) (headI (outer z)) ++ cut (original z) (headI (inner z))) ++
        [false, false]))).length ≤ z.length + measure z := by
    simp only [pack_length, measure, original, outer, inner, output, List.length_append,
      List.length_cons, List.length_nil] at *
    omega
  simp only [step, sel]
  split
  · omega
  · split
    · split
      · exact hadv
      · split <;> assumption
    · exact hadv

def seed (x : Word) : Word := pack x x (dropI x) []

def compile (x : Word) : Word := output (step^[x.length * x.length + x.length] (seed x))

theorem compile_cpt : CPT compile := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime_measure step m measure 5 (by
    intro z
    simp [measure, original_step]) step_length (by
    intro z
    have h := unpairB_length z
    unfold measure original
    omega)
  have hs : CPT seed := cpt_pairB2 cpt_id (cpt_pairB2 cpt_id (cpt_pairB2 cpt_dropI (cpt_const [])))
  have hclock := cpt_app2 (cpt_mulU2 cpt_id cpt_id) cpt_id
  have hout : CPT output := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  exact cptl (cpt_comp (cpt_comp (cpt_pair hs hclock) loop) hout) (fun x => by
    simp [compile, mulU, un_length])

def ready (x r acc : Word) : Word := pack x r (dropI r) acc

theorem step_pair (x : Word) (l d : Literal) (o i acc : Word)
    (hl : (encodeLiteral l).length ≤ x.length) (hd : (encodeLiteral d).length ≤ x.length) :
    step (pack x (encodeLiteral l ++ o) (encodeLiteral d ++ i) acc) =
      pack x (encodeLiteral l ++ o) i (acc ++ encodeClause [l, d]) := by
  have hn₁ : encodeLiteral l ++ o ≠ [] := by simp [encodeLiteral_eq]
  have hn₂ : encodeLiteral d ++ i ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, original, outer, inner, output, unpairB_pairB, sel, hn₁, hn₂,
    isEnd_lit, bflag, Bool.false_eq_true, ite_false, headI_lit, dropI_lit, cut_eq,
    List.take_of_length_le hl, List.take_of_length_le hd]
  simp [encodeClause, List.append_assoc]

theorem step_row (x : Word) (l : Literal) (r i acc : Word) (h : r.length ≤ x.length) :
    step (pack x (encodeLiteral l ++ r) ([false, false] ++ i) acc) = ready x r acc := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  have h' := (dropI_length r).trans h
  simp only [step, ready, pack, original, outer, inner, output, unpairB_pairB, sel, hn,
    isEnd_lit, bflag, Bool.false_eq_true, ite_false, dropI_lit, cut_eq, List.take_of_length_le h']
  simp [isEnd]

theorem step_close (x r acc : Word) (h : r.length ≤ x.length) :
    step (ready x ([false, false] ++ r) acc) = ready x r acc := by
  have h' := (dropI_length r).trans h
  simp [step, ready, pack, original, outer, inner, output, unpairB_pairB, sel, isEnd,
    bflag, dropI, cut_eq, List.take_of_length_le h']

theorem step_empty (x acc : Word) : step (ready x [] acc) = ready x [] acc := by
  simp [step, ready, pack, original, outer, unpairB_pairB, sel]

theorem row_scan (x : Word) (l : Literal) (c : Clause) (o r acc : Word)
    (hl : (encodeLiteral l).length ≤ x.length)
    (hc : (c.flatMap encodeLiteral ++ r).length ≤ x.length) :
    step^[c.length] (pack x (encodeLiteral l ++ o) (c.flatMap encodeLiteral ++ r) acc) =
      pack x (encodeLiteral l ++ o) r (acc ++ encodeCNF (c.map (fun d => [l, d]))) := by
  induction c generalizing acc with
  | nil => simp [encodeCNF]
  | cons d c ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.length_append] at hc
    have hd : (encodeLiteral d).length ≤ x.length := by omega
    have ht : (c.flatMap encodeLiteral ++ r).length ≤ x.length := by simp only [List.length_append]; omega
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_pair x l d o _ acc hl hd]
    rw [ih _ ht]
    simp [encodeCNF, List.append_assoc]

def clauseWork : Clause → ℕ
  | [] => 1
  | _ :: c => clauseWork c + (c.length + 1)

def totalWork (φ : CNF) : ℕ := (φ.map clauseWork).sum

theorem clause_scan (x : Word) (c : Clause) (r acc : Word)
    (h : (encodeClause c ++ r).length ≤ x.length) :
    step^[clauseWork c] (ready x (encodeClause c ++ r) acc) =
      ready x r (acc ++ encodeCNF (pairClauses c)) := by
  induction c generalizing acc with
  | nil =>
    simpa [clauseWork, pairClauses, encodeClause, encodeCNF] using step_close x r acc
      (show r.length ≤ x.length by simp [encodeClause] at h; omega)
  | cons l c ih =>
    have he : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
      simp [encodeClause, List.append_assoc]
    rw [he] at h ⊢
    have hl : (encodeLiteral l).length ≤ x.length := by
      simp only [List.length_append] at h
      omega
    have ht : (encodeClause c ++ r).length ≤ x.length := by
      simp only [List.length_append] at h ⊢
      omega
    have htail : encodeClause c ++ r = c.flatMap encodeLiteral ++ ([false, false] ++ r) := by
      simp [encodeClause, List.append_assoc]
    have hrow := row_scan x l c (encodeClause c ++ r) ([false, false] ++ r) acc hl (htail ▸ ht)
    have hready : ready x (encodeLiteral l ++ (encodeClause c ++ r)) acc =
        pack x (encodeLiteral l ++ (encodeClause c ++ r))
          (c.flatMap encodeLiteral ++ ([false, false] ++ r)) acc := by
      unfold ready
      rw [dropI_lit, htail]
    rw [hready, clauseWork, Function.iterate_add_apply, Function.iterate_succ_apply', hrow,
      step_row _ _ _ _ _ ht, ih _ ht]
    simp [pairClauses, encodeCNF, List.flatMap_append, List.append_assoc]

theorem cnf_scan (x : Word) (φ : CNF) (acc : Word)
    (h : (encodeCNF φ).length ≤ x.length) :
    step^[totalWork φ] (ready x (encodeCNF φ) acc) =
      ready x [] (acc ++ encodeCNF (pairCNF φ)) := by
  induction φ generalizing acc with
  | nil => simp [totalWork, encodeCNF, pairCNF]
  | cons c cs ih =>
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := rfl
    rw [he] at h ⊢
    have htail : (encodeCNF cs).length ≤ x.length := by simp only [List.length_append] at h; omega
    have hw : totalWork (c :: cs) = totalWork cs + clauseWork c := by
      simp [totalWork, Nat.add_comm]
    rw [hw, Function.iterate_add_apply, clause_scan _ _ _ _ h, ih _ htail]
    simp [pairCNF, encodeCNF, List.flatMap_append, List.append_assoc]

theorem clauseWork_bound (c : Clause) : clauseWork c ≤ (c.length + 1)^2 := by
  induction c with
  | nil => decide
  | cons l c ih =>
    simp only [clauseWork, List.length_cons]
    nlinarith

theorem totalWork_bound (φ : CNF) : totalWork φ ≤ (nIt φ)^2 := by
  induction φ with
  | nil => decide
  | cons c cs ih =>
    have hc := clauseWork_bound c
    have hp : 0 ≤ (c.length + 1) * nIt cs := Nat.zero_le _
    simp only [totalWork, List.map_cons, List.sum_cons, nIt] at *
    nlinarith

theorem compile_enc (φ : CNF) : compile (encodeCNF φ) = encodeCNF (pairCNF φ) := by
  let x := encodeCNF φ
  have hnum : totalWork φ ≤ x.length * x.length + x.length :=
    ((totalWork_bound φ).trans (Nat.pow_le_pow_left (nIt_le φ) 2)).trans (by simp only [pow_two, x]; omega)
  have hs := cnf_scan x φ [] le_rfl
  have hf := step_empty x (encodeCNF (pairCNF φ))
  change output (step^[x.length * x.length + x.length] (ready x x [])) = _
  simp only [List.nil_append] at hs
  rw [← Nat.sub_add_cancel hnum, Function.iterate_add_apply, hs, Function.iterate_fixed hf]
  simp [ready, output, pack, unpairB_pairB]

end PEqualNP.Outside.HornRenamingCompiler
