import PEqualNP.Outside.FirstWideCollector

namespace PEqualNP.Outside.FirstWideClause

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.FirstWideCollector

def firstWide (φ : CNF) : Option Clause := φ.find? (fun c => decide (2 < c.length))

def names (c : Clause) : Word := (c.map Prod.fst).flatMap vcode

theorem step_lit (l : Literal) (r b : Word) (n : ℕ) :
    step (pack (encodeLiteral l ++ r) (un n) b []) =
      pack r (un (n + 1)) (b ++ vcode l.1) [] := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, isEnd_lit,
    bflag, Bool.false_eq_true, ite_false, ite_true, sel, hne, headI_lit, dropI_lit]
  simp [encodeLiteral_eq, un, List.replicate_succ]

theorem step_close (r b : Word) (n : ℕ) :
    step (pack ([false, false] ++ r) (un n) b []) =
      pack r [] [] (if 2 < n then b else []) := by
  have hnil : (un n).tail.tail = [] ↔ ¬ 2 < n := by
    rw [List.eq_nil_iff_length_eq_zero]
    simp only [List.length_tail, un_length]
    omega
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, dropI, isEnd,
    bflag, ite_true, sel, List.cons_ne_nil, ite_false, List.cons_append, List.nil_append, hnil]
  by_cases hn : 2 < n <;> simp [hn]

theorem step_stop (r n b o : Word) (h : o ≠ []) :
    step (pack r n b o) = pack r n b o := by
  simp [step, pack, out, unpairB_pairB, sel, h]

theorem step_empty : step (pack [] [] [] []) = pack [] [] [] [] := by
  simp [step, pack, out, rest, unpairB_pairB, sel]

theorem names_ne_nil (c : Clause) (hn : c ≠ []) : names c ≠ [] := by
  cases c with
  | nil => contradiction
  | cons a c => simp [names, vcode_ne_nil]

theorem clause_loop (c : Clause) (r b : Word) (n : ℕ) :
    step^[c.length] (pack (c.flatMap encodeLiteral ++ r) (un n) b []) =
      pack r (un (n + c.length)) (b ++ names c) [] := by
  induction c generalizing b n with
  | nil => simp [names]
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit]
    simpa [names, List.flatMap_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using ih (b ++ vcode l.1) (n + 1)

theorem clause_close (c : Clause) (r : Word) :
    step^[c.length + 1] (pack (encodeClause c ++ r) [] [] []) =
      pack r [] [] (if 2 < c.length then names c else []) := by
  rw [Function.iterate_succ_apply']
  have h := clause_loop c ([false, false] ++ r) [] 0
  simp only [un_zero, Nat.zero_add, List.nil_append] at h
  simp only [encodeClause, List.append_assoc]
  rw [h]
  exact step_close _ _ _

theorem cnf_loop (φ : CNF) :
    let z := step^[nIt φ] (pack (encodeCNF φ) [] [] [])
    match firstWide φ with
    | none => z = pack [] [] [] []
    | some c => ∃ r, z = pack r [] [] (names c) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := rfl
    rw [hn, Function.iterate_add_apply, he, clause_close]
    by_cases hc : 2 < c.length
    · have hn : names c ≠ [] := names_ne_nil c (by intro h; simp [h] at hc)
      simp [firstWide, List.find?_cons, hc, Function.iterate_fixed (step_stop _ _ _ _ hn)]
      exact ⟨_, rfl⟩
    · simpa [firstWide, List.find?_cons, hc] using ih

theorem gather_enc (φ : CNF) :
    gather (encodeCNF φ) = ((firstWide φ).map names).getD [] := by
  have h := cnf_loop φ
  have hn := nIt_le φ
  unfold gather
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  cases hc : firstWide φ with
  | none =>
    simp only [hc] at h
    rw [h, Function.iterate_fixed step_empty]
    simp [out, pack, unpairB_pairB]
  | some c =>
    simp only [hc] at h
    obtain ⟨r, he⟩ := h
    have hlen : 2 < c.length := of_decide_eq_true (List.find?_some (p := fun d : Clause => decide (2 < d.length)) hc)
    have hn : names c ≠ [] := names_ne_nil c (by intro e; simp [e] at hlen)
    rw [he, Function.iterate_fixed (step_stop _ _ _ _ hn)]
    simp [out, pack, unpairB_pairB]

theorem firstWide_some {φ : CNF} {c : Clause} (h : firstWide φ = some c) :
    c ∈ φ ∧ 2 < c.length :=
  ⟨List.mem_of_find?_eq_some h, of_decide_eq_true (List.find?_some (p := fun d : Clause => decide (2 < d.length)) h)⟩

theorem firstWide_none (φ : CNF) : firstWide φ = none ↔ IsKCNF 2 φ := by
  simp only [firstWide, List.find?_eq_none, IsKCNF]
  constructor
  · intro h c hc
    have := h c hc
    simp at this
    omega
  · intro h c hc
    have := h c hc
    simp
    omega

end PEqualNP.Outside.FirstWideClause
