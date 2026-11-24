import PEqualNP.Outside.PrefixNameCollector

namespace PEqualNP.Outside.PrefixClauseNames

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.PrefixNameCollector

def prefixNames (φ : CNF) : List ℕ :=
  φ.flatMap (fun c => (c.take (c.length - 2)).map Prod.fst)

theorem step_lit (l : Literal) (r u v b o : Word) :
    step (pack (encodeLiteral l ++ r) u v b o) =
      pack r v (vcode l.1) (b ++ u) o := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, rest, older, newer, buf, out, unpairB_pairB, isEnd_lit,
    bflag, Bool.false_eq_true, ite_false, sel, hne, headI_lit, dropI_lit]
  simp [encodeLiteral_eq]

theorem step_close (r u v b o : Word) :
    step (pack ([false, false] ++ r) u v b o) = pack r [] [] [] (o ++ b) := by
  simp [step, pack, rest, older, newer, buf, out, unpairB_pairB, isEnd, dropI, sel, bflag]

theorem step_end (o : Word) : step (pack [] [] [] [] o) = pack [] [] [] [] o := by
  simp [step, pack, rest, unpairB_pairB, sel]

theorem loop_shift (c : Clause) (u v : Literal) (r b o : Word) :
    ∃ u' v' : Word,
      step^[c.length] (pack (c.flatMap encodeLiteral ++ r) (vcode u.1) (vcode v.1) b o) =
        pack r u' v'
          (b ++ (((u :: v :: c).take c.length).map Prod.fst).flatMap vcode) o := by
  induction c generalizing u v b with
  | nil => exact ⟨vcode u.1, vcode v.1, by simp⟩
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit]
    obtain ⟨u', v', h⟩ := ih v l (b ++ vcode u.1)
    exact ⟨u', v', by simpa [List.append_assoc] using h⟩

theorem loop_clause (c : Clause) (r o : Word) :
    step^[c.length] (pack (c.flatMap encodeLiteral ++ r) [] [] [] o) =
      let future := step^[c.length] (pack (c.flatMap encodeLiteral ++ r) [] [] [] o)
      pack r (older future) (newer future)
        (((c.take (c.length - 2)).map Prod.fst).flatMap vcode) o := by
  cases c with
  | nil => simp [pack, older, newer, unpairB_pairB]
  | cons l c =>
    cases c with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Function.iterate_one,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, step_lit]
      simp [pack, older, newer, unpairB_pairB]
    | cons m c =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [List.flatMap_cons, List.append_assoc, step_lit, List.nil_append, List.append_nil]
      obtain ⟨u, v, h⟩ := loop_shift c l m r [] o
      rw [h]
      simp [pack, older, newer, unpairB_pairB, h, Nat.add_assoc]

theorem clause_close (c : Clause) (r o : Word) :
    step^[c.length + 1] (pack (encodeClause c ++ r) [] [] [] o) =
      pack r [] [] [] (o ++ (((c.take (c.length - 2)).map Prod.fst).flatMap vcode)) := by
  rw [Function.iterate_succ_apply']
  simp only [encodeClause, List.append_assoc]
  conv_lhs => arg 1; rw [loop_clause]
  exact step_close _ _ _ _ _

theorem cnf_loop (φ : CNF) (o : Word) :
    step^[nIt φ] (pack (encodeCNF φ) [] [] [] o) =
      pack [] [] [] [] (o ++ (prefixNames φ).flatMap vcode) := by
  induction φ generalizing o with
  | nil => simp [nIt, encodeCNF, prefixNames]
  | cons c φ ih =>
    have hn : nIt (c :: φ) = nIt φ + (c.length + 1) := by simp [nIt, Nat.add_comm]
    rw [hn, Function.iterate_add_apply]
    have he : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := rfl
    rw [he, clause_close, ih]
    simp [prefixNames, List.flatMap_append, List.append_assoc]

theorem collect_enc (φ : CNF) :
    collect (encodeCNF φ) = (prefixNames φ).flatMap vcode := by
  have hm := nIt_le φ
  unfold collect
  rw [← Nat.sub_add_cancel hm, Function.iterate_add_apply, cnf_loop, List.nil_append,
    Function.iterate_fixed (step_end _)]
  simp [out, pack, unpairB_pairB]

end PEqualNP.Outside.PrefixClauseNames
