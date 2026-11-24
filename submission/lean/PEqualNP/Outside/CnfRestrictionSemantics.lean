import PEqualNP.Outside.CnfRestrictionMachine
import PEqualNP.Outside.RestrictCnfHelpers

namespace PEqualNP.Outside.CnfRestrictionSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.CnfRestrictionMachine

def valueOf (a b : List ℕ) (i : ℕ) : Option Bool :=
  if i ∈ a then some (decide (i ∈ b)) else none

def names (a : List ℕ) : Word := a.flatMap vcode

theorem step_on_literal (a b : List ℕ) (l : Literal) (r c out : Word) (f : Bool) :
    step (pack (names a) (names b) (encodeLiteral l ++ r) c (bflag f) out) =
      pack (names a) (names b) r
        (if (valueOf a b l.1).isNone then c ++ encodeLiteral l else c)
        (bflag (f || (valueOf a b l.1 == some l.2))) out := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  have ha : memB (vcode l.1) (names a) = decide (l.1 ∈ a) := by
    exact Bool.eq_iff_iff.mpr ((asg_codes a l.1).trans (by simp))
  have hb : memB (vcode l.1) (names b) = decide (l.1 ∈ b) := by
    exact Bool.eq_iff_iff.mpr ((asg_codes b l.1).trans (by simp))
  simp only [step, pack, assigned, trueNames, rest, clause, satisfied, result,
    unpairB_pairB, headI_lit, dropI_lit, isEnd_lit, literalFlag_spec, sel, hne, ite_false]
  by_cases hA : l.1 ∈ a
  · by_cases hB : l.1 ∈ b
    · cases hp : l.2 <;> cases f <;>
        simp [encodeLiteral_eq, polB, ha, hb, hA, hB, hp, bflag, valueOf]
    · cases hp : l.2 <;> cases f <;>
        simp [encodeLiteral_eq, polB, ha, hb, hA, hB, hp, bflag, valueOf]
  · simp [encodeLiteral_eq, polB, ha, hA, bflag, valueOf]

theorem step_on_close (a b : List ℕ) (r c out : Word) (f : Bool) :
    step (pack (names a) (names b) ([false, false] ++ r) c (bflag f) out) =
      pack (names a) (names b) r [] [] (if f then out else out ++ c ++ [false, false]) := by
  cases f <;> simp [step, pack, assigned, trueNames, rest, clause, satisfied, result,
    unpairB_pairB, isEnd, dropI, sel, bflag]

theorem step_at_end (a b : List ℕ) (out : Word) :
    step (pack (names a) (names b) [] [] [] out) =
      pack (names a) (names b) [] [] [] out := by
  simp [step, pack, rest, unpairB_pairB, sel]

theorem run_clause_items (a b : List ℕ) (c : Clause) (r buf out : Word) (f : Bool) :
    let isOpen := fun l : Literal => (valueOf a b l.1).isNone
    let isTrue := fun l : Literal => valueOf a b l.1 == some l.2
    step^[c.length] (pack (names a) (names b) (c.flatMap encodeLiteral ++ r) buf (bflag f) out) =
      pack (names a) (names b) r (buf ++ (c.filter isOpen).flatMap encodeLiteral)
        (bflag (f || c.any isTrue)) out := by
  induction c generalizing buf f with
  | nil => simp
  | cons l c ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons,
      List.append_assoc, step_on_literal]
    cases h : valueOf a b l.1 with
    | none =>
      simpa [h, List.filter_cons, List.flatMap_cons, List.append_assoc] using
        ih (buf ++ encodeLiteral l) f
    | some v =>
      cases hval : (v == l.2)
      · simpa [h, hval, List.filter_cons, Bool.or_assoc] using ih buf f
      · simpa [h, hval, List.filter_cons, Bool.or_assoc] using ih buf true

theorem run_clause (a b : List ℕ) (c : Clause) (r out : Word) :
    step^[c.length + 1] (pack (names a) (names b) (encodeClause c ++ r) [] [] out) =
      pack (names a) (names b) r [] []
        (if c.any (fun l => valueOf a b l.1 == some l.2) then out
          else out ++ encodeClause (c.filter (fun l => (valueOf a b l.1).isNone))) := by
  rw [Function.iterate_succ_apply']
  have h := run_clause_items a b c ([false, false] ++ r) [] out false
  simp only [Bool.false_or, bflag, Bool.false_eq_true, ite_false, List.nil_append] at h
  simp only [encodeClause, List.append_assoc]
  rw [h]
  simpa [List.append_assoc, bflag] using step_on_close a b r
    ((c.filter (fun l => (valueOf a b l.1).isNone)).flatMap encodeLiteral) out
      (c.any (fun l => valueOf a b l.1 == some l.2))

theorem run_cnf_items (a b : List ℕ) (φ : CNF) (out : Word) :
    step^[nIt φ] (pack (names a) (names b) (encodeCNF φ) [] [] out) =
      pack (names a) (names b) [] [] []
        (out ++ encodeCNF (RestrictCnfHelpers.restrict (valueOf a b) φ)) := by
  induction φ generalizing out with
  | nil => simp [nIt, encodeCNF, RestrictCnfHelpers.restrict]
  | cons c φ ih =>
    have hn : nIt (c :: φ) = nIt φ + (c.length + 1) := by simp [nIt, Nat.add_comm]
    rw [hn, Function.iterate_add_apply]
    have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := rfl
    rw [he, run_clause, ih]
    cases hs : c.any (fun l => valueOf a b l.1 == some l.2) <;>
      simp [RestrictCnfHelpers.restrict, hs, encodeCNF, List.append_assoc]

theorem run_enc (a b : List ℕ) (φ : CNF) :
    run (encodeCNF φ, pairB (names a) (names b)) =
      encodeCNF (RestrictCnfHelpers.restrict (valueOf a b) φ) := by
  have hm := nIt_le φ
  change result (step^[(encodeCNF φ).length]
    (pack (unpairB (pairB (names a) (names b))).1 (unpairB (pairB (names a) (names b))).2
      (encodeCNF φ) [] [] [])) = _
  rw [unpairB_pairB, ← Nat.sub_add_cancel hm, Function.iterate_add_apply, run_cnf_items,
    Function.iterate_fixed (step_at_end _ _ _)]
  simp [result, pack, unpairB_pairB]

end PEqualNP.Outside.CnfRestrictionSemantics
