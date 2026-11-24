import PEqualNP.Outside.LexModelGateFacts
import PEqualNP.Outside.CnfRestrictionMachine
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.LexModelGateCompiler

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Search
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Outside.LexModelGateFacts (shift lead gate encode_shift)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def marker : Word := encodeLiteral (0, true)

def renameItem (w : Word) : Word :=
  sel (bflag (polB w)) (true :: false :: true :: true :: (headI w).tail.tail)
    (true :: true :: true :: true :: (headI w).tail.tail)

theorem renameItem_time : CPT renameItem := by
  have ht := cpt_tail1 (cpt_tail1 cpt_headI)
  have hn := cpt_cons1 true (cpt_cons1 false (cpt_cons1 true (cpt_cons1 true ht)))
  have hp := cpt_cons1 true (cpt_cons1 true (cpt_cons1 true (cpt_cons1 true ht)))
  exact cptl (cpt_sel PEqualNP.Library.SearchHelpers.TwoSat.cpt_polF hn hp) (fun _ => rfl)

theorem renameItem_length (w : Word) : (renameItem w).length ≤ (headI w).length + 4 := by
  unfold renameItem sel
  split <;> simp <;> omega

def addon (w : Word) : Word := sel w [] marker

def step (z : Word) : Word :=
  let r := (unpairB z).1
  let a := (unpairB z).2
  let t := dropI r
  let more := sel (bflag (isEnd r)) (renameItem r) ([false, false] ++ addon t)
  sel r z (pairB t (a ++ more))

theorem step_cpt : CPT step := by
  have hr := cpt_unpairB1
  have ht := cpt_comp hr cpt_dropI
  have hm := cpt_sel (cpt_comp hr cpt_isEndF) (cpt_comp hr renameItem_time)
    (cpt_app2 (cpt_const [false, false]) (cpt_sel ht (cpt_const []) (cpt_const marker)))
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 ht (cpt_app2 cpt_unpairB2 hm))) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 7 := by
  have h := unpairB_length z
  have ht := congrArg List.length (headI_dropI (unpairB z).1)
  have hm := renameItem_length (unpairB z).1
  have hn : (addon (dropI (unpairB z).1)).length ≤ 4 := by
    unfold addon sel
    split
    · decide
    · decide
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length, List.length_append]
    split
    · omega
    · have hmore : ([false, false] ++ addon (dropI (unpairB z).1)).length ≤ 6 := by
        rw [List.length_append]
        change 2 + (addon (dropI (unpairB z).1)).length ≤ 6
        omega
      omega

def ready (r a : Word) : Word := pairB r (a ++ addon r)

def compile (w : Word) : Word := (unpairB (step^[w.length] (ready w (encodeClause lead)))).2

theorem compile_cpt : CPT compile := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 7 step_length
  have hs : CPT (fun w => ready w (encodeClause lead)) :=
    cpt_pairB2 cpt_id (cpt_app2 (cpt_const (encodeClause lead)) (cpt_sel cpt_id (cpt_const []) (cpt_const marker)))
  have h := cpt_comp (cpt_comp (cpt_pair hs cpt_id) loop) cpt_unpairB2
  exact h

theorem step_lit (l : Literal) (r a : Word) :
    step (pairB (encodeLiteral l ++ r) a) = pairB r (a ++ encodeLiteral (shift l)) := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, sel, unpairB_pairB, hn, ite_false, isEnd_lit, bflag, Bool.false_eq_true,
    dropI_lit, renameItem, headI_lit, encode_shift]
  rcases l with ⟨i, b⟩
  cases b <;> simp [encodeLiteral_eq, polB, bflag, sel]

theorem step_close (r a : Word) :
    step (pairB ([false, false] ++ r) a) = ready r (a ++ [false, false]) := by
  simp [step, ready, sel, unpairB_pairB, isEnd, bflag, dropI, List.append_assoc]

theorem scan_clause (c : Clause) (r a : Word) :
    step^[c.length] (pairB (c.flatMap encodeLiteral ++ r) a) =
      pairB r (a ++ (c.map shift).flatMap encodeLiteral) := by
  induction c generalizing a with
  | nil => simp
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit, ih, List.map_cons]

theorem scan (φ : CNF) (a : Word) :
    step^[nIt φ] (ready (encodeCNF φ) a) =
      pairB [] (a ++ encodeCNF (φ.map (fun c => (0, true) :: c.map shift))) := by
  induction φ generalizing a with
  | nil => simp [nIt, encodeCNF, ready, addon, sel]
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = c.flatMap encodeLiteral ++ ([false, false] ++ encodeCNF cs) := by
      simp [encodeCNF, encodeClause, List.append_assoc]
    have hp : ready (encodeCNF (c :: cs)) a = pairB (encodeCNF (c :: cs)) (a ++ marker) := by
      have hne : encodeCNF (c :: cs) ≠ [] := by
        rw [he]
        simp
      simp [ready, addon, sel, hne]
    rw [hp, hn, he, Function.iterate_add_apply, Function.iterate_succ_apply', scan_clause, step_close, ih]
    simp [marker, encodeCNF, encodeClause, List.append_assoc]

theorem compile_enc (φ : CNF) : compile (encodeCNF φ) = encodeCNF (gate φ) := by
  have h := scan φ (encodeClause lead)
  have hn := nIt_le φ
  have hf : step (pairB [] (encodeCNF (gate φ))) = pairB [] (encodeCNF (gate φ)) := by
    simp [step, sel, unpairB_pairB]
  change (unpairB (step^[(encodeCNF φ).length] (ready (encodeCNF φ) (encodeClause lead)))).2 = _
  change step^[nIt φ] (ready (encodeCNF φ) (encodeClause lead)) = pairB [] (encodeCNF (gate φ)) at h
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, h, Function.iterate_fixed hf, unpairB_pairB]

end PEqualNP.Outside.LexModelGateCompiler
