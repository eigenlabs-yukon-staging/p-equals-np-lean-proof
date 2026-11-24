import PEqualNP.Outside.CnfRestrictionMachine
import PEqualNP.Library.Machines.LenLE

namespace PEqualNP.Outside.MaxClauseWidthMachine

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def rest (z : Word) : Word := (unpairB z).1
def count (z : Word) : Word := (unpairB (unpairB z).2).1
def largest (z : Word) : Word := (unpairB (unpairB z).2).2
def pack (r n m : Word) : Word := pairB r (pairB n m)

def larger (n m : Word) : Word :=
  sel (bflag (decide (n.length ≤ m.length))) n m

def step (z : Word) : Word :=
  let r := rest z
  let n := count z
  let m := largest z
  let tail := dropI r
  sel r z (sel (bflag (isEnd r)) (pack tail (true :: n) m) (pack tail [] (larger n m)))

theorem larger_cpt {n m : Word → Word} (hn : CPT n) (hm : CPT m) :
    CPT (fun z => larger (n z) (m z)) := by
  have hCompare := cpt_bitFlag (cpt_comp (cpt_pair hm hn) LenCmp.lenLE_polyTime)
  exact cptl (cpt_sel hCompare hn hm) (fun _ => rfl)

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have hn : CPT count := cpt_unpairB1_1 cpt_unpairB2
  have hm : CPT largest := cpt_unpairB2_1 cpt_unpairB2
  have ht := cpt_comp hr cpt_dropI
  have hlit := cpt_pairB2 ht (cpt_pairB2 (cpt_cons1 true hn) hm)
  have hclose := cpt_pairB2 ht (cpt_pairB2 (cpt_const []) (larger_cpt hn hm))
  exact cptl (cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF) hlit hclose)) (fun _ => rfl)

theorem larger_length (n m : Word) : (larger n m).length ≤ n.length + m.length := by
  unfold larger sel
  split <;> omega

theorem step_length (z : Word) : (step z).length ≤ z.length + 4 := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := dropI_length (rest z)
  have h₄ := larger_length (count z) (largest z)
  simp only [step, sel]
  split
  · omega
  · split
    · simp only [pack, pairB_length, List.length_cons, rest, count, largest] at h₃ h₄ ⊢
      omega
    · simp only [pack, pairB_length, List.length_nil, rest, count, largest] at h₃ h₄ ⊢
      omega

def clock (x : Word) : Word := largest (step^[x.length] (pack x [] []))

theorem clock_cpt : CPT clock := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 4 step_length
  have seed := cpt_pairB2 cpt_id (cpt_const (pairB [] []))
  have h := cpt_comp (cpt_comp (cpt_pair seed cpt_id) loop) (cpt_unpairB2_1 cpt_unpairB2)
  exact h

def maxWidth : CNF → ℕ
  | [] => 0
  | c :: cs => max c.length (maxWidth cs)

theorem larger_un (n m : ℕ) : larger (un n) (un m) = un (max n m) := by
  by_cases h : n ≤ m
  · simp [larger, sel, bflag, un_length, h, max_eq_right h]
  · have hm : m ≤ n := by omega
    simp [larger, sel, bflag, un_length, h, max_eq_left hm]

theorem step_lit (l : Literal) (r : Word) (n m : ℕ) :
    step (pack (encodeLiteral l ++ r) (un n) (un m)) =
      pack r (un (n + 1)) (un m) := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, rest, count, largest, unpairB_pairB, isEnd_lit,
    bflag, Bool.false_eq_true, ite_false, sel, hne, dropI_lit]
  simp [un, List.replicate_succ]

theorem step_close (r : Word) (n m : ℕ) :
    step (pack ([false, false] ++ r) (un n) (un m)) =
      pack r [] (un (max n m)) := by
  simp [step, pack, rest, count, largest, unpairB_pairB, isEnd, dropI, sel, bflag, larger_un]

theorem step_end (m : ℕ) : step (pack [] [] (un m)) = pack [] [] (un m) := by
  simp [step, rest, pack, unpairB_pairB, sel]

theorem clause_loop (c : Clause) (r : Word) (n m : ℕ) :
    step^[c.length] (pack (c.flatMap encodeLiteral ++ r) (un n) (un m)) =
      pack r (un (n + c.length)) (un m) := by
  induction c generalizing n with
  | nil => simp
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

theorem clause_close (c : Clause) (r : Word) (m : ℕ) :
    step^[c.length + 1] (pack (encodeClause c ++ r) [] (un m)) =
      pack r [] (un (max c.length m)) := by
  rw [Function.iterate_succ_apply']
  have h := clause_loop c ([false, false] ++ r) 0 m
  simp only [un_zero, Nat.zero_add] at h
  simp only [encodeClause, List.append_assoc]
  rw [h]
  exact step_close _ _ _

theorem cnf_loop (φ : CNF) (m : ℕ) :
    step^[nIt φ] (pack (encodeCNF φ) [] (un m)) =
      pack [] [] (un (max (maxWidth φ) m)) := by
  induction φ generalizing m with
  | nil => simp [nIt, encodeCNF, maxWidth]
  | cons c φ ih =>
    have hn : nIt (c :: φ) = nIt φ + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := rfl
    rw [hn, Function.iterate_add_apply, he, clause_close, ih]
    simp [maxWidth, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]

theorem clock_enc (φ : CNF) : clock (encodeCNF φ) = un (maxWidth φ) := by
  have hn := nIt_le φ
  change largest (step^[(encodeCNF φ).length] (pack (encodeCNF φ) [] (un 0))) = _
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, cnf_loop,
    Function.iterate_fixed (step_end _)]
  simp [largest, pack, unpairB_pairB]

end PEqualNP.Outside.MaxClauseWidthMachine
