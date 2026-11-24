import PEqualNP.Outside.LongClauseCollector

namespace PEqualNP.Outside.LongClauseNames

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.LongClauseCollector

def longNames (φ : CNF) : List ℕ :=
  φ.flatMap (fun c => if 2 < c.length then c.map Prod.fst else [])

theorem step_lit (l : Literal) (r b o : Word) (n : ℕ) :
    step (pack (encodeLiteral l ++ r) (un n) b o) =
      pack r (un (n + 1)) (b ++ vcode l.1) o := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, isEnd_lit,
    bflag, Bool.false_eq_true, ite_false, sel, hne, headI_lit, dropI_lit]
  simp [encodeLiteral_eq, un, List.replicate_succ]

theorem step_close (r b o : Word) (n : ℕ) :
    step (pack ([false, false] ++ r) (un n) b o) =
      pack r [] [] (if 2 < n then o ++ b else o) := by
  have hnil : (un n).tail.tail = [] ↔ ¬ 2 < n := by
    rw [List.eq_nil_iff_length_eq_zero]
    simp only [List.length_tail, un_length]
    omega
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, dropI, isEnd,
    bflag, ite_true, sel, List.cons_ne_nil, ite_false, List.cons_append, List.nil_append, hnil]
  by_cases hn : 2 < n <;> simp [hn]

theorem step_end (o : Word) : step (pack [] [] [] o) = pack [] [] [] o := by
  simp [step, pack, rest, unpairB_pairB, sel]

theorem clause_loop (c : Clause) (r b o : Word) (n : ℕ) :
    step^[c.length] (pack (c.flatMap encodeLiteral ++ r) (un n) b o) =
      pack r (un (n + c.length)) (b ++ (c.map Prod.fst).flatMap vcode) o := by
  induction c generalizing b n with
  | nil => simp
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit]
    simpa [List.flatMap_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using ih (b ++ vcode l.1) (n + 1)

theorem clause_close (c : Clause) (r o : Word) :
    step^[c.length + 1] (pack (encodeClause c ++ r) [] [] o) =
      pack r [] [] (if 2 < c.length then o ++ (c.map Prod.fst).flatMap vcode else o) := by
  rw [Function.iterate_succ_apply']
  have h := clause_loop c ([false, false] ++ r) [] o 0
  simp only [un_zero, Nat.zero_add, List.nil_append] at h
  simp only [encodeClause, List.append_assoc]
  rw [h]
  exact step_close _ _ _ _

theorem cnf_loop (φ : CNF) (o : Word) :
    step^[nIt φ] (pack (encodeCNF φ) [] [] o) =
      pack [] [] [] (o ++ (longNames φ).flatMap vcode) := by
  induction φ generalizing o with
  | nil => simp [nIt, encodeCNF, longNames]
  | cons c φ ih =>
    have hn : nIt (c :: φ) = nIt φ + (c.length + 1) := by simp [nIt, Nat.add_comm]
    rw [hn, Function.iterate_add_apply]
    have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := rfl
    rw [he, clause_close, ih]
    by_cases hc : 2 < c.length <;>
      simp [longNames, hc, List.flatMap_append, List.append_assoc]

theorem gather_enc (φ : CNF) :
    gather (encodeCNF φ) = (longNames φ).flatMap vcode := by
  have hm := nIt_le φ
  unfold gather
  rw [← Nat.sub_add_cancel hm, Function.iterate_add_apply, cnf_loop, List.nil_append,
    Function.iterate_fixed (step_end _)]
  simp [out, pack, unpairB_pairB]

end PEqualNP.Outside.LongClauseNames
