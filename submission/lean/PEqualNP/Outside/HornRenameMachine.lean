import PEqualNP.Outside.HornRenamingFacts
import PEqualNP.Outside.CnfRestrictionSemantics
import PEqualNP.Outside.FirstWideCollector
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.HornRenameMachine

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.FirstWideCollector (Word rest count buf out pack pack_length state_bound)
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Outside.CnfRestrictionSemantics (names)
open PEqualNP.Outside.HornRenamingFacts (rename renameClause)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def signed (r v : Word) : Word :=
  let code := (headI r).tail.tail
  let set := bflag (memB code v)
  let pol := bflag (polB r)
  let pos := true :: true :: code
  let neg := true :: false :: code
  sel pol (sel set neg pos) (sel set pos neg)

theorem signed_cpt {r v : Word → Word} (hr : CPT r) (hv : CPT v) :
    CPT (fun z => signed (r z) (v z)) := by
  have hcode := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have hset := cpt_memB hcode hv
  have hpol := cpt_comp hr PEqualNP.Library.SearchHelpers.TwoSat.cpt_polF
  have hp := cpt_cons1 true (cpt_cons1 true hcode)
  have hn := cpt_cons1 true (cpt_cons1 false hcode)
  exact cptl (cpt_sel hpol (cpt_sel hset hn hp) (cpt_sel hset hp hn)) (fun _ => rfl)

theorem signed_length (r v : Word) : (signed r v).length ≤ (headI r).length + 2 := by
  simp only [signed, sel]
  split <;> split <;> simp <;> omega

def step (z : Word) : Word :=
  let r := rest z
  let v := count z
  let acc := out z
  let piece := sel (bflag (isEnd r)) (signed r v) (headI r)
  sel r z (pack (dropI r) v [] (acc ++ piece))

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have hv : CPT count := cpt_unpairB1_1 cpt_unpairB2
  have hacc : CPT out := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have ht := cpt_comp hr cpt_dropI
  have hp := cpt_sel (cpt_comp hr cpt_isEndF) (signed_cpt hr hv) (cpt_comp hr cpt_headI)
  exact cptl (cpt_sel hr cpt_id
    (cpt_pairB2 ht (cpt_pairB2 hv (cpt_pairB2 (cpt_const []) (cpt_app2 hacc hp)))))
    (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 5 := by
  have h := state_bound z
  have hs := signed_length (rest z) (count z)
  have ht := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · omega
  · simp only [pack_length, List.length_append, List.length_nil]
    split <;> omega

def run (q : Word × Word) : Word := out (step^[q.1.length] (pack q.1 q.2 [] []))

theorem run_cpt : ComputableInPolyTime encodePair (fun x : Word => x) run := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 5 step_length
  have seed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const (pairB [] []))))
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 q.2 [] []) :=
    cptl seed (fun _ => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_comp (cpt_pairG hs cpt_fst) loop)
    (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact h

def flips (k : List ℕ) : Assignment := fun i => decide (i ∈ k)

theorem signed_enc (l : Literal) (r : Word) (k : List ℕ) :
    signed (encodeLiteral l ++ r) (names k) = encodeLiteral (l.1, xor l.2 (flips k l.1)) := by
  have hmem : memB (vcode l.1) (names k) = flips k l.1 := by
    unfold flips
    by_cases h : l.1 ∈ k
    · have he : memB (vcode l.1) (names k) = true := (asg_codes k l.1).mpr h
      rw [he]
      simp [h]
    · cases he : memB (vcode l.1) (names k)
      · simp [h]
      · exact False.elim (h ((asg_codes k l.1).mp he))
  unfold signed
  rw [headI_lit]
  rcases l with ⟨i, b⟩
  cases b <;> cases h : flips k i <;>
    simp_all [encodeLiteral_eq, polB, bflag, sel]

theorem step_lit (l : Literal) (r a : Word) (k : List ℕ) :
    step (pack (encodeLiteral l ++ r) (names k) [] a) =
      pack r (names k) [] (a ++ encodeLiteral (l.1, xor l.2 (flips k l.1))) := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp [step, pack, rest, count, out, sel, unpairB_pairB, hn, isEnd_lit, dropI_lit, bflag,
    signed_enc]

theorem step_close (r a : Word) (k : List ℕ) :
    step (pack ([false, false] ++ r) (names k) [] a) =
      pack r (names k) [] (a ++ [false, false]) := by
  simp [step, pack, rest, count, out, unpairB_pairB, isEnd, headI, dropI, sel, bflag]

theorem scan_clause (c : Clause) (r a : Word) (k : List ℕ) :
    step^[c.length] (pack (c.flatMap encodeLiteral ++ r) (names k) [] a) =
      pack r (names k) [] (a ++ (renameClause (flips k) c).flatMap encodeLiteral) := by
  induction c generalizing a with
  | nil => simp [renameClause]
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit, ih, renameClause, List.map_cons]

theorem scan (φ : CNF) (k : List ℕ) (a : Word) :
    step^[nIt φ] (pack (encodeCNF φ) (names k) [] a) =
      pack [] (names k) [] (a ++ encodeCNF (rename (flips k) φ)) := by
  induction φ generalizing a with
  | nil => simp [nIt, rename, encodeCNF]
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = c.flatMap encodeLiteral ++ ([false, false] ++ encodeCNF cs) := by
      simp [encodeCNF, encodeClause, List.append_assoc]
    rw [hn, he, Function.iterate_add_apply, Function.iterate_succ_apply', scan_clause, step_close, ih]
    simp [rename, encodeCNF, encodeClause, List.append_assoc]

theorem run_enc (φ : CNF) (k : List ℕ) :
    run (encodeCNF φ, names k) = encodeCNF (rename (flips k) φ) := by
  have hn := nIt_le φ
  have he := scan φ k []
  have hfix : step (pack [] (names k) [] (encodeCNF (rename (flips k) φ))) =
      pack [] (names k) [] (encodeCNF (rename (flips k) φ)) := by
    simp [step, pack, rest, unpairB_pairB, sel]
  change out (step^[(encodeCNF φ).length] (pack (encodeCNF φ) (names k) [] [])) = _
  simp only [List.nil_append] at he
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, he, Function.iterate_fixed hfix]
  simp [out, pack, unpairB_pairB]

end PEqualNP.Outside.HornRenameMachine
