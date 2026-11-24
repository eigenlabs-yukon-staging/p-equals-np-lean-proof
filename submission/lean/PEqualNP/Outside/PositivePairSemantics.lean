import PEqualNP.Outside.PositivePairMachine
import PEqualNP.Outside.CnfRestrictionSemantics

namespace PEqualNP.Outside.PositivePairSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.CnfRestrictionSemantics (names)
open PEqualNP.Outside.PositivePairMachine

abbrev NamePair := ℕ × ℕ

def encodeNames (t : NamePair) : Word := pairB (vcode t.1) (vcode t.2)

def codeAt (vs : List ℕ) (i : ℕ) : Word := (vs[i]?.map vcode).getD []

def pending (a : List ℕ) (r : Word) (vs : List ℕ) : Word :=
  pack (names a) r (codeAt vs 0) []

def locked (a : List ℕ) (r : Word) (t : NamePair) : Word :=
  pack (names a) r [] (encodeNames t)

def pairs (vs : List ℕ) : Option NamePair :=
  match vs with
  | i :: j :: _ => some (i, j)
  | _ => none

def unassigned (a : List ℕ) (c : Clause) : List ℕ :=
  (c.filter (fun l => l.2 && decide (l.1 ∉ a))).map Prod.fst

theorem step_locked (a : List ℕ) (r : Word) (t : NamePair) :
    step (locked a r t) = locked a r t := by
  have hn : encodeNames t ≠ [] := by simp [encodeNames, pairB]
  simp [locked, step, found, pack, unpairB_pairB, sel, hn]

theorem step_empty (a : List ℕ) : step (pending a [] []) = pending a [] [] := by
  simp [pending, step, rest, found, pack, unpairB_pairB, sel]

theorem step_close (a : List ℕ) (r : Word) (vs : List ℕ) :
    step (pending a ([false, false] ++ r) vs) = pending a r [] := by
  simp [pending, step, pack, known, rest, first, found, unpairB_pairB, sel,
    isEnd, dropI, bflag, codeAt]

theorem step_known (a : List ℕ) (l : Literal) (r : Word) (vs : List ℕ) (h : l.1 ∈ a) :
    step (pending a (encodeLiteral l ++ r) vs) = pending a r vs := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  have hb : memB (vcode l.1) (names a) = true := (asg_codes a l.1).mpr h
  simp only [pending, step, pack, known, rest, first, found, unpairB_pairB, sel,
    isEnd_lit, bflag, Bool.false_eq_true, ite_false, hn, headI_lit, dropI_lit]
  cases l.2 <;> simp [encodeLiteral_eq, polB, hb]

theorem step_negative (a : List ℕ) (l : Literal) (r : Word) (vs : List ℕ) (h : l.2 = false) :
    step (pending a (encodeLiteral l ++ r) vs) = pending a r vs := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [pending, step, pack, known, rest, first, found, unpairB_pairB, sel,
    isEnd_lit, bflag, Bool.false_eq_true, ite_false, hn, headI_lit, dropI_lit]
  simp [encodeLiteral_eq, polB, h]

theorem step_open (a : List ℕ) (l : Literal) (r : Word) (vs : List ℕ)
    (hp : l.2 = true) (h : l.1 ∉ a) (hv : vs.length ≤ 1) :
    step (pending a (encodeLiteral l ++ r) vs) =
      match pairs (vs ++ [l.1]) with
      | none => pending a r (vs ++ [l.1])
      | some t => locked a r t := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  have hb : memB (vcode l.1) (names a) = false := by
    cases ht : memB (vcode l.1) (names a)
    · rfl
    · exact False.elim (h ((asg_codes a l.1).mp ht))
  simp only [pending, step, pack, known, rest, first, found, unpairB_pairB, sel,
    isEnd_lit, bflag, Bool.false_eq_true, ite_false, hn, headI_lit, dropI_lit]
  rcases vs with _ | ⟨i, tail⟩
  · simp [encodeLiteral_eq, hb, hp, polB, pairs, codeAt]
  · have e : tail = [] := by simpa using hv
    subst tail
    simp [encodeLiteral_eq, hb, hp, polB, pairs, codeAt, vcode_ne_nil, locked, encodeNames, pack]

theorem clause_scan (a : List ℕ) (c : Clause) (r : Word) (vs : List ℕ) (hv : vs.length ≤ 1) :
    let z := step^[c.length] (pending a (c.flatMap encodeLiteral ++ r) vs)
    match pairs (vs ++ unassigned a c) with
    | none => z = pending a r (vs ++ unassigned a c)
    | some t => ∃ suffix, z = locked a suffix t := by
  induction c generalizing vs with
  | nil =>
    have ht : pairs vs = none := by
      rcases vs with _ | ⟨i, _ | ⟨j, tail⟩⟩ <;> simp_all [pairs]
    simp [unassigned, ht]
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc]
    cases hp : l.2
    · rw [step_negative a l _ vs hp]
      simpa [unassigned, hp] using ih vs hv
    · by_cases h : l.1 ∈ a
      · rw [step_known a l _ vs h]
        simpa [unassigned, h] using ih vs hv
      · rw [step_open a l _ vs hp h hv]
        have hu : unassigned a (l :: c) = l.1 :: unassigned a c := by
          simp [unassigned, h, hp]
        rw [hu, ← List.singleton_append, ← List.append_assoc]
        cases ht : pairs (vs ++ [l.1]) with
        | none =>
          have hlen : (vs ++ [l.1]).length ≤ 1 := by
            rcases vs with _ | ⟨i, _ | ⟨j, tail⟩⟩ <;> simp_all [pairs]
          simpa only [ht] using ih (vs ++ [l.1]) hlen
        | some t =>
          have hext : pairs ((vs ++ [l.1]) ++ unassigned a c) = some t := by
            rcases vs with _ | ⟨i, _ | ⟨j, tail⟩⟩ <;> simp_all [pairs]
          simp only [ht, hext, Function.iterate_fixed (step_locked _ _ _)]
          exact ⟨_, rfl⟩

def firstBad (a : List ℕ) : CNF → Option NamePair
  | [] => none
  | c :: cs => (pairs (unassigned a c)).orElse (fun _ => firstBad a cs)

theorem cnf_scan (a : List ℕ) (φ : CNF) :
    let z := step^[nIt φ] (pending a (encodeCNF φ) [])
    match firstBad a φ with
    | none => z = pending a [] []
    | some t => ∃ suffix, z = locked a suffix t := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have hg := clause_scan a c ([false, false] ++ encodeCNF cs) [] (by simp)
    simp only [List.nil_append] at hg
    rw [hn, Function.iterate_add_apply, Function.iterate_succ_apply']
    have he : encodeCNF (c :: cs) =
        c.flatMap encodeLiteral ++ ([false, false] ++ encodeCNF cs) := by
      change encodeClause c ++ encodeCNF cs = _
      simp [encodeClause, List.append_assoc]
    rw [he]
    cases h : pairs (unassigned a c) with
    | none =>
      simp only [h] at hg
      rw [hg, step_close]
      simpa [firstBad, h] using ih
    | some t =>
      simp only [h] at hg
      obtain ⟨suffix, heq⟩ := hg
      rw [heq, step_locked, Function.iterate_fixed (step_locked _ _ _)]
      simpa [firstBad, h] using (show ∃ r, locked a suffix t = locked a r t from ⟨suffix, rfl⟩)

theorem obstruction_enc (a : List ℕ) (φ : CNF) :
    obstruction (encodeCNF φ, names a) =
      ((firstBad a φ).map encodeNames).getD [] := by
  have hn := nIt_le φ
  have h := cnf_scan a φ
  change found (step^[(encodeCNF φ).length] (pending a (encodeCNF φ) [])) = _
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  cases ht : firstBad a φ with
  | none =>
    simp only [ht] at h
    rw [h, Function.iterate_fixed (step_empty _)]
    simp [pending, found, pack, unpairB_pairB]
  | some t =>
    simp only [ht] at h
    obtain ⟨suffix, h⟩ := h
    rw [h, Function.iterate_fixed (step_locked _ _ _)]
    simp [locked, found, pack, unpairB_pairB]

theorem pairs_none (vs : List ℕ) : pairs vs = none ↔ vs.length ≤ 1 := by
  rcases vs with _ | ⟨i, _ | ⟨j, tail⟩⟩ <;> simp [pairs]

theorem firstBad_none (a : List ℕ) (φ : CNF) :
    firstBad a φ = none ↔ ∀ c ∈ φ, (c.filter (fun l => l.2 && decide (l.1 ∉ a))).length ≤ 1 := by
  induction φ with
  | nil => simp [firstBad]
  | cons c cs ih =>
    cases h : pairs (unassigned a c) with
    | none =>
      have hw := (pairs_none (unassigned a c)).mp h
      simp only [unassigned, List.length_map] at hw
      constructor
      · intro he c' hc'
        rcases List.mem_cons.mp hc' with rfl | hm
        · exact hw
        · exact (ih.mp (by simpa [firstBad, h] using he)) c' hm
      · intro hh
        have he := ih.mpr (fun c' hc' => hh c' (List.mem_cons_of_mem _ hc'))
        simpa [firstBad, h] using he
    | some t =>
      have hw : ¬ (c.filter (fun l => l.2 && decide (l.1 ∉ a))).length ≤ 1 := by
        intro hb
        have hnone := (pairs_none (unassigned a c)).mpr (by simpa [unassigned] using hb)
        rw [h] at hnone
        cases hnone
      constructor
      · intro he
        simp [firstBad, h] at he
      · intro hh
        exact False.elim (hw (hh c (by simp)))

theorem firstBad_some (a : List ℕ) (φ : CNF) (t : NamePair) (h : firstBad a φ = some t) :
    ∃ c ∈ φ, ∃ tail, unassigned a c = t.1 :: t.2 :: tail := by
  induction φ with
  | nil => simp [firstBad] at h
  | cons c cs ih =>
    cases ht : pairs (unassigned a c) with
    | none =>
      have h' : firstBad a cs = some t := by simpa [firstBad, ht] using h
      obtain ⟨c', hc', tail, hEq⟩ := ih h'
      exact ⟨c', List.mem_cons_of_mem _ hc', tail, hEq⟩
    | some u =>
      have e : u = t := by simpa [firstBad, ht] using h
      subst t
      refine ⟨c, by simp, ?_⟩
      cases he : unassigned a c with
      | nil => simp [he, pairs] at ht
      | cons x s =>
        rcases s with _ | ⟨y, tail⟩
        · simp [he, pairs] at ht
        · simp [he, pairs] at ht
          subst u
          exact ⟨tail, rfl⟩

end PEqualNP.Outside.PositivePairSemantics
