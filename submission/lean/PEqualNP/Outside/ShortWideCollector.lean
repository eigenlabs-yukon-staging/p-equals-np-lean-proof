import PEqualNP.Outside.FirstWideClause
import PEqualNP.Outside.NameDigitClock
import PEqualNP.Library.Machines.LenLE

namespace PEqualNP.Outside.ShortWideCollector

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.FirstWideCollector (Word rest count buf out pack pack_length state_bound)
open PEqualNP.Outside.FirstWideClause (names)
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def preferWord (n b o : Word) : Word :=
  sel n.tail.tail o
    (sel o b (sel (bflag (decide ((NameDigitClock.count o).length ≤ n.length))) b o))

theorem prefer_cpt {n b o : Word → Word} (hn : CPT n) (hb : CPT b) (ho : CPT o) :
    CPT (fun z => preferWord (n z) (b z) (o z)) := by
  have ht := cpt_bitFlag (cpt_comp (cpt_pair hn (cpt_comp ho NameDigitClock.count_cpt)) LenCmp.lenLE_polyTime)
  exact cptl (cpt_sel (cpt_tail1 (cpt_tail1 hn)) ho (cpt_sel ho hb (cpt_sel ht hb ho)))
    (fun _ => rfl)

theorem prefer_length (n b o : Word) : (preferWord n b o).length ≤ b.length + o.length := by
  unfold preferWord sel
  split
  · omega
  · split
    · omega
    · split <;> omega

def step (z : Word) : Word :=
  let r := rest z
  let n := count z
  let b := buf z
  let o := out z
  let suffix := dropI r
  let lit := pack suffix (true :: n) (b ++ (headI r).tail.tail) o
  let close := pack suffix [] [] (preferWord n b o)
  sel r z (sel (bflag (isEnd r)) lit close)

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have hn : CPT count := cpt_unpairB1_1 cpt_unpairB2
  have h₃ := cpt_unpairB2_1 cpt_unpairB2
  have hb : CPT buf := cpt_unpairB1_1 h₃
  have ho : CPT out := cpt_unpairB2_1 h₃
  have ht := cpt_comp hr cpt_dropI
  have hName := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have hlit := cpt_pairB2 ht (cpt_pairB2 (cpt_cons1 true hn) (cpt_pairB2 (cpt_app2 hb hName) ho))
  have hclose := cpt_pairB2 ht (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (prefer_cpt hn hb ho)))
  exact cptl (cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF) hlit hclose)) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 5 := by
  have h := state_bound z
  have hp := prefer_length (count z) (buf z) (out z)
  have ht := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · omega
  · split
    · simp only [pack_length, List.length_cons, List.length_append, List.length_tail]
      omega
    · simp only [pack_length, List.length_nil]
      omega

def gather (x : Word) : Word := out (step^[x.length] (pack x [] [] []))

theorem gather_cpt : CPT gather := by
  obtain ⟨c⟩ := step_cpt
  have loop := Iter.iter_polyTime step c 5 step_length
  have hs := cpt_pairB2 cpt_id (cpt_const (pairB [] (pairB [] [])))
  have h := cpt_comp (cpt_comp (cpt_pair hs cpt_id) loop)
    (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact h

def prefer (best : Option Clause) (c : Clause) : Option Clause :=
  if 2 < c.length then best.elim (some c) (fun old => if c.length < old.length then some c else best)
  else best

def shortest (φ : CNF) : Option Clause := φ.foldl prefer none

def namesOf (c : Option Clause) : Word := (c.map names).getD []

theorem prefer_enc (best : Option Clause) (c : Clause)
    (hbest : ∀ old ∈ best, 2 < (old : Clause).length) :
    preferWord (un c.length) (names c) (namesOf best) = namesOf (prefer best c) := by
  have hz : (un c.length).tail.tail = [] ↔ ¬ 2 < c.length := by
    rw [List.eq_nil_iff_length_eq_zero]
    simp only [List.length_tail, un_length]
    omega
  by_cases hc : 2 < c.length
  · cases best with
    | none => simp [preferWord, prefer, namesOf, hc, sel, hz]
    | some old =>
      have hlen := hbest old rfl
      have hne := FirstWideClause.names_ne_nil old (by intro e; simp [e] at hlen)
      have hn : NameDigitClock.count (names old) = un old.length := by
        unfold names
        rw [NameDigitClock.count_codes, List.length_map]
      by_cases h : c.length < old.length
      · simp [preferWord, prefer, namesOf, hc, sel, hz, hne, hn, un_length, h, Nat.not_le_of_lt h, bflag]
      · simp [preferWord, prefer, namesOf, hc, sel, hz, hne, hn, un_length, h, Nat.le_of_not_gt h, bflag]
  · simp [preferWord, prefer, hc, sel, hz]

theorem step_lit (l : Literal) (r b o : Word) (n : ℕ) :
    step (pack (encodeLiteral l ++ r) (un n) b o) =
      pack r (un (n + 1)) (b ++ vcode l.1) o := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, isEnd_lit,
    bflag, Bool.false_eq_true, ite_false, ite_true, sel, hne, headI_lit, dropI_lit]
  simp [encodeLiteral_eq, un, List.replicate_succ]

theorem step_close (r b o : Word) (n : ℕ) :
    step (pack ([false, false] ++ r) (un n) b o) =
      pack r [] [] (preferWord (un n) b o) := by
  simp [step, pack, rest, count, buf, out, unpairB_pairB, dropI, isEnd, bflag, sel]

theorem clause_loop (c : Clause) (r b o : Word) (n : ℕ) :
    step^[c.length] (pack (c.flatMap encodeLiteral ++ r) (un n) b o) =
      pack r (un (n + c.length)) (b ++ names c) o := by
  induction c generalizing b n with
  | nil => simp [names]
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit]
    simpa [names, List.flatMap_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using ih (b ++ vcode l.1) (n + 1)

theorem clause_close (c : Clause) (r : Word) (best : Option Clause)
    (h : ∀ old ∈ best, 2 < (old : Clause).length) :
    step^[c.length + 1] (pack (encodeClause c ++ r) [] [] (namesOf best)) =
      pack r [] [] (namesOf (prefer best c)) := by
  rw [Function.iterate_succ_apply']
  have he := clause_loop c ([false, false] ++ r) [] (namesOf best) 0
  simp only [un_zero, Nat.zero_add, List.nil_append] at he
  simp only [encodeClause, List.append_assoc]
  rw [he, step_close, prefer_enc best c h]

theorem prefer_wide (best : Option Clause) (c : Clause)
    (h : ∀ old ∈ best, 2 < (old : Clause).length) :
    ∀ old ∈ prefer best c, 2 < (old : Clause).length := by
  intro old ho
  unfold prefer at ho
  split at ho
  · rename_i hc
    cases best with
    | none =>
      simp at ho
      simpa [ho] using hc
    | some d =>
      simp only [Option.elim_some] at ho
      split at ho
      · simp at ho
        simpa [ho] using hc
      · exact h old ho
  · exact h old ho

theorem scan (φ : CNF) (best : Option Clause) (h : ∀ old ∈ best, 2 < (old : Clause).length) :
    step^[nIt φ] (pack (encodeCNF φ) [] [] (namesOf best)) =
      pack [] [] [] (namesOf (φ.foldl prefer best)) := by
  induction φ generalizing best with
  | nil => rfl
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := rfl
    rw [hn, Function.iterate_add_apply, he, clause_close _ _ _ h]
    exact ih _ (prefer_wide best c h)

theorem gather_enc (φ : CNF) : gather (encodeCNF φ) = namesOf (shortest φ) := by
  unfold gather
  have hn := nIt_le φ
  have hfix : step (pack [] [] [] (namesOf (shortest φ))) = pack [] [] [] (namesOf (shortest φ)) := by
    simp [step, pack, rest, sel, unpairB_pairB]
  have hs := scan φ none (by simp)
  change step^[nIt φ] (pack (encodeCNF φ) [] [] []) = pack [] [] [] (namesOf (shortest φ)) at hs
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, hs, Function.iterate_fixed hfix]
  simp [out, pack, unpairB_pairB]

def Candidate (xs : CNF) (best : Option Clause) : Prop :=
  match best with
  | none => IsKCNF 2 xs
  | some c => c ∈ xs ∧ 2 < c.length ∧ ∀ d ∈ xs, 2 < d.length → c.length ≤ d.length

private theorem prefer_candidate (xs : CNF) (best : Option Clause) (c : Clause)
    (h : Candidate xs best) : Candidate (c :: xs) (prefer best c) := by
  cases best with
  | none =>
    change IsKCNF 2 xs at h
    by_cases hc : 2 < c.length
    · simp only [prefer, if_pos hc, Option.elim_none, Candidate]
      refine ⟨by simp, hc, ?_⟩
      intro d hd hw
      rcases List.mem_cons.mp hd with rfl | ha
      · rfl
      · exact False.elim ((Nat.not_lt_of_ge (h _ ha)) hw)
    · simp only [prefer, if_neg hc, Candidate]
      intro d hd
      rcases List.mem_cons.mp hd with rfl | ha
      · omega
      · exact h _ ha
  | some old =>
    obtain ⟨ho, hwide, hmin⟩ := h
    by_cases hc : 2 < c.length
    · by_cases hs : c.length < old.length
      · simp only [prefer, if_pos hc, Option.elim_some, if_pos hs, Candidate]
        refine ⟨by simp, hc, ?_⟩
        intro d hd hw
        rcases List.mem_cons.mp hd with rfl | ha
        · rfl
        · exact hs.le.trans (hmin _ ha hw)
      · simp only [prefer, if_pos hc, Option.elim_some, if_neg hs, Candidate]
        refine ⟨by simp [ho], hwide, ?_⟩
        intro d hd hw
        rcases List.mem_cons.mp hd with rfl | ha
        · omega
        · exact hmin _ ha hw
    · simp only [prefer, if_neg hc, Candidate]
      refine ⟨by simp [ho], hwide, ?_⟩
      intro d hd hw
      rcases List.mem_cons.mp hd with rfl | ha
      · omega
      · exact hmin _ ha hw

private theorem fold_candidate (φ xs : CNF) (best : Option Clause)
    (h : Candidate xs best) : Candidate (φ.reverse ++ xs) (φ.foldl prefer best) := by
  induction φ generalizing xs best with
  | nil => simpa using h
  | cons c cs ih =>
    simpa [List.append_assoc] using ih (c :: xs) (prefer best c) (prefer_candidate xs best c h)

theorem shortest_some {φ : CNF} {c : Clause} (h : shortest φ = some c) :
    c ∈ φ ∧ 2 < c.length ∧ ∀ d ∈ φ, 2 < d.length → c.length ≤ d.length := by
  have hp := fold_candidate φ [] none (by simp [Candidate, IsKCNF])
  change Candidate (φ.reverse ++ []) (shortest φ) at hp
  simpa [h, Candidate] using hp

theorem shortest_none (φ : CNF) : shortest φ = none ↔ IsKCNF 2 φ := by
  constructor
  · intro h
    have hp := fold_candidate φ [] none (by simp [Candidate, IsKCNF])
    change Candidate (φ.reverse ++ []) (shortest φ) at hp
    simpa [h, Candidate, IsKCNF] using hp
  · intro h
    cases hc : shortest φ with
    | none => rfl
    | some c =>
      obtain ⟨hm, hw, _⟩ := shortest_some hc
      exact False.elim ((Nat.not_lt_of_ge (h _ hm)) hw)

end PEqualNP.Outside.ShortWideCollector
