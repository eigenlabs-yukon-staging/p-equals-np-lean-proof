import PEqualNP.Outside.FirstWideClause
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.PositiveClauseCollector

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.FirstWideCollector (Word rest count buf out pack pack_length state_bound)
open PEqualNP.Outside.FirstWideClause (names names_ne_nil)
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def unitValue (b : Word) : Word := sel b [] (sel (dropI b) b [])

theorem unitValue_cpt {b : Word → Word} (hb : CPT b) : CPT (fun z => unitValue (b z)) :=
  cptl (cpt_sel hb (cpt_const []) (cpt_sel (cpt_comp hb cpt_dropI) hb (cpt_const []))) (fun _ => rfl)

def closeValue (unit : Bool) (n b : Word) : Word :=
  sel n (if unit then unitValue b else [true]) []

theorem closeValue_cpt (unit : Bool) {n b : Word → Word} (hn : CPT n) (hb : CPT b) :
    CPT (fun z => closeValue unit (n z) (b z)) := by
  cases unit
  · exact cptl (cpt_sel hn (cpt_const [true]) (cpt_const [])) (fun _ => rfl)
  · exact cptl (cpt_sel hn (unitValue_cpt hb) (cpt_const [])) (fun _ => rfl)

theorem closeValue_length (unit : Bool) (n b : Word) : (closeValue unit n b).length ≤ b.length + 1 := by
  unfold closeValue sel
  split
  · cases unit
    · simp
    · unfold unitValue
      change (sel b [] (sel (dropI b) b [])).length ≤ b.length + 1
      unfold sel
      split
      · simp
      · split <;> simp
  · simp

def step (unit : Bool) (z : Word) : Word :=
  let r := rest z
  let n := count z
  let b := buf z
  let o := out z
  let suffix := dropI r
  let lit := pack suffix (sel (bflag (polB r)) [true] n) (b ++ (headI r).tail.tail) o
  let close := pack suffix [] [] (closeValue unit n b)
  sel o (sel r z (sel (bflag (isEnd r)) lit close)) z

theorem step_cpt (unit : Bool) : CPT (step unit) := by
  have hr : CPT rest := cpt_unpairB1
  have hn : CPT count := cpt_unpairB1_1 cpt_unpairB2
  have h₃ := cpt_unpairB2_1 cpt_unpairB2
  have hb : CPT buf := cpt_unpairB1_1 h₃
  have ho : CPT out := cpt_unpairB2_1 h₃
  have ht := cpt_comp hr cpt_dropI
  have hName := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have hNeg := cpt_sel (cpt_comp hr PEqualNP.Library.SearchHelpers.TwoSat.cpt_polF) (cpt_const [true]) hn
  have hlit := cpt_pairB2 ht (cpt_pairB2 hNeg (cpt_pairB2 (cpt_app2 hb hName) ho))
  have hclose := cpt_pairB2 ht (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (closeValue_cpt unit hn hb)))
  exact cptl (cpt_sel ho (cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF) hlit hclose)) cpt_id)
    (fun _ => rfl)

theorem step_length (unit : Bool) (z : Word) : (step unit z).length ≤ z.length + 5 := by
  have h := state_bound z
  have hp := closeValue_length unit (count z) (buf z)
  have ht := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · split
    · omega
    · split
      · simp only [pack_length, List.length_append, List.length_tail]
        split <;> simp_all <;> omega
      · simp only [pack_length, List.length_nil]
        omega
  · omega

def gather (unit : Bool) (x : Word) : Word := out ((step unit)^[x.length] (pack x [] [] []))

theorem gather_cpt (unit : Bool) : CPT (gather unit) := by
  obtain ⟨m⟩ := step_cpt unit
  have loop := Iter.iter_polyTime (step unit) m 5 (step_length unit)
  have hs := cpt_pairB2 cpt_id (cpt_const (pairB [] (pairB [] [])))
  have h := cpt_comp (cpt_comp (cpt_pair hs cpt_id) loop)
    (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact h

def qualifies (unit : Bool) (c : Clause) : Bool :=
  c.all Prod.snd && (!unit || decide (c.length = 1))

def pick (unit : Bool) (φ : CNF) : Option Clause := φ.find? (qualifies unit)

def result (unit : Bool) (c : Clause) : Word := if unit then names c else [true]

theorem unitValue_enc (c : Clause) :
    unitValue (names c) = if c.length = 1 then names c else [] := by
  cases c with
  | nil => simp [unitValue, sel, names]
  | cons l c =>
    cases c with
    | nil =>
      have hd := dropI_vcode l.1 ([] : Word)
      simp only [List.append_nil] at hd
      simp [unitValue, sel, names, hd, vcode_ne_nil]
    | cons a cs => simp [unitValue, sel, names, dropI_vcode, vcode_ne_nil]

theorem result_ne_nil (unit : Bool) (c : Clause) (h : qualifies unit c = true) :
    result unit c ≠ [] := by
  cases unit
  · simp [result]
  · have hn : c.length = 1 := by
      simp [qualifies] at h
      exact h.2
    have hne : c ≠ [] := by intro e; simp [e] at hn
    simpa [result] using names_ne_nil c hne

theorem step_lit (unit : Bool) (l : Literal) (r b : Word) (neg : Bool) :
    step unit (pack (encodeLiteral l ++ r) (bflag neg) b []) =
      pack r (bflag (neg || !l.2)) (b ++ vcode l.1) [] := by
  have hne : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, isEnd_lit,
    Bool.false_eq_true, ite_false, ite_true, sel, hne, headI_lit, dropI_lit]
  rcases l with ⟨i, p⟩
  cases p <;> cases neg <;> simp [encodeLiteral_eq, polB, bflag]

theorem clause_loop (unit : Bool) (c : Clause) (r b : Word) (neg : Bool) :
    (step unit)^[c.length] (pack (c.flatMap encodeLiteral ++ r) (bflag neg) b []) =
      pack r (bflag (neg || !(c.all Prod.snd))) (b ++ names c) [] := by
  induction c generalizing b neg with
  | nil => simp [names]
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit, ih, List.all_cons]
    have h : ((neg || !l.2) || !(c.all Prod.snd)) = (neg || !(l.2 && c.all Prod.snd)) := by
      cases neg <;> cases l.2 <;> cases c.all Prod.snd <;> rfl
    rw [h]
    simp [names, List.append_assoc]

theorem step_close (unit : Bool) (c : Clause) (r : Word) :
    step unit (pack ([false, false] ++ r) (bflag (!(c.all Prod.snd))) (names c) []) =
      pack r [] [] (if qualifies unit c then result unit c else []) := by
  simp only [step, pack, rest, count, buf, out, unpairB_pairB, dropI, isEnd, bflag, sel,
    List.nil_append, List.cons_append, List.cons_ne_nil, ite_false, ite_true]
  change pack r [] [] (closeValue unit (bflag (!(c.all Prod.snd))) (names c)) = _
  cases unit <;> cases h : c.all Prod.snd <;> simp [closeValue, qualifies, result, h, bflag, sel, unitValue_enc, pack]

theorem clause_close (unit : Bool) (c : Clause) (r : Word) :
    (step unit)^[c.length + 1] (pack (encodeClause c ++ r) [] [] []) =
      pack r [] [] (if qualifies unit c then result unit c else []) := by
  rw [Function.iterate_succ_apply']
  have h := clause_loop unit c ([false, false] ++ r) [] false
  simp only [bflag, Bool.false_eq_true, ite_false, Bool.false_or, List.nil_append] at h
  simp only [encodeClause, List.append_assoc]
  rw [h]
  exact step_close unit c r

theorem step_stop (unit : Bool) (r n b o : Word) (h : o ≠ []) :
    step unit (pack r n b o) = pack r n b o := by
  simp [step, pack, out, unpairB_pairB, sel, h]

theorem step_empty (unit : Bool) : step unit (pack [] [] [] []) = pack [] [] [] [] := by
  simp [step, pack, out, rest, unpairB_pairB, sel]

theorem scan (unit : Bool) (φ : CNF) :
    let z := (step unit)^[nIt φ] (pack (encodeCNF φ) [] [] [])
    match pick unit φ with
    | none => z = pack [] [] [] []
    | some c => ∃ r, z = pack r [] [] (result unit c) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := rfl
    rw [hn, Function.iterate_add_apply, he, clause_close]
    cases hc : qualifies unit c
    · simpa [pick, hc] using ih
    · have hne := result_ne_nil unit c hc
      simp [pick, hc, Function.iterate_fixed (step_stop unit _ _ _ _ hne)]
      exact ⟨_, rfl⟩

theorem gather_enc (unit : Bool) (φ : CNF) :
    gather unit (encodeCNF φ) = ((pick unit φ).map (result unit)).getD [] := by
  have h := scan unit φ
  have hn := nIt_le φ
  unfold gather
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  cases hc : pick unit φ with
  | none =>
    simp only [hc] at h
    rw [h, Function.iterate_fixed (step_empty unit)]
    simp [out, pack, unpairB_pairB]
  | some c =>
    simp only [hc] at h
    obtain ⟨r, he⟩ := h
    have hn := result_ne_nil unit c (List.find?_some hc)
    rw [he, Function.iterate_fixed (step_stop unit _ _ _ _ hn)]
    simp [out, pack, unpairB_pairB]

end PEqualNP.Outside.PositiveClauseCollector
