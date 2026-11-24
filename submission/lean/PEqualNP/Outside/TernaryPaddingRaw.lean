import PEqualNP.Outside.TernaryPaddingEmit
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.SearchHelpers.TwoSatStr

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.SatCodePrimitives (cptl)
open PEqualNP.Outside.CNFWidth (Word evenLit evenLit_len evenLit_cpt evenLit_enc)
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF)
open PEqualNP.Library.SearchHelpers.SatV (vcode vcode_injective)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def conflict (a b : Word) : Word :=
  sel (bflag (decide (a.tail.tail = b.tail.tail))) [] (sel (bflag (decide (a=b))) [true] [])

theorem conflict_cpt {a b : Word → Word} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => conflict (a s) (b s)) :=
  cpt_sel (cpt_eqF (cpt_tail1 (cpt_tail1 ha)) (cpt_tail1 (cpt_tail1 hb))) (cpt_const [])
    (cpt_sel (cpt_eqF ha hb) (cpt_const [true]) (cpt_const []))

def keep (a b : Word) : Word := sel (bflag (decide (a=b))) a []

theorem keep_cpt {a b : Word → Word} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => keep (a s) (b s)) := cpt_sel (cpt_eqF ha hb) ha (cpt_const [])

def present (a : Word) : Word := sel a [] [true]

theorem present_cpt : CPT present := cpt_sel cpt_id (cpt_const []) (cpt_const [true])

def completeWord (b t : Word) : Word :=
  sel t (localWord (localFormula 3) b)
    (sel t.tail (localWord (localFormula 2) b)
      (sel t.tail.tail (localWord (localFormula 1) b) (localWord (localFormula 0) b)))

theorem completeWord_cpt {b t : Word → Word} (hb : CPT b) (ht : CPT t) :
    CPT (fun s => completeWord (b s) (t s)) := by
  have h (n : ℕ) := cpt_comp hb (localWord_cpt (localFormula n))
  exact cpt_sel ht (h 3) (cpt_sel (cpt_tail1 ht) (h 2)
    (cpt_sel (cpt_tail1 (cpt_tail1 ht)) (h 1) (h 0)))

theorem completeWord_spec (base t : Word) (h : t.length ≤ 3) :
    completeWord base t = localWord (localFormula (3-t.length)) base := by
  rcases t with _ | ⟨_,_ | ⟨_,_ | ⟨_,ts⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · have ht : ts = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
    subst ts
    rfl

def carry (base a b c : Word) : Word :=
  let p := keep (keep a b) c
  let q := keep b c
  evenLit false p ++ evenLit false q ++ evenLit false c ++
    completeWord base (present p ++ present q ++ present c)

def emitRaw (base a b c : Word) : Word :=
  sel (conflict a b ++ conflict a c ++ conflict b c) (carry base a b c) []

theorem carry_cpt {a b c base : Word → Word} (ha : CPT a) (hb : CPT b) (hc : CPT c) (hbase : CPT base) :
    CPT (fun x => carry (base x) (a x) (b x) (c x)) := by
  have hp := keep_cpt (keep_cpt ha hb) hc
  have hq := keep_cpt hb hc
  have hcount := cpt_app2 (cpt_app2 (cpt_comp hp present_cpt) (cpt_comp hq present_cpt))
    (cpt_comp hc present_cpt)
  exact cptl (cpt_app2
    (cpt_app2 (cpt_app2 (cpt_comp hp (evenLit_cpt false)) (cpt_comp hq (evenLit_cpt false)))
      (cpt_comp hc (evenLit_cpt false)))
    (completeWord_cpt hbase hcount)) (fun _ => rfl)

theorem emitRaw_cpt {a b c base : Word → Word} (ha : CPT a) (hb : CPT b) (hc : CPT c)
    (hbase : CPT base) : CPT (fun x => emitRaw (base x) (a x) (b x) (c x)) :=
  cpt_sel (cpt_app2 (cpt_app2 (conflict_cpt ha hb) (conflict_cpt ha hc)) (conflict_cpt hb hc))
    (carry_cpt ha hb hc hbase) (cpt_const [])

theorem keep_len (a b : Word) : (keep a b).length ≤ a.length := by
  unfold keep sel
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem completeWord_len : ∃ K, ∀ base t : Word, (completeWord base t).length ≤ K*(base.length+1) := by
  obtain ⟨k0,h0⟩ := localWord_len (localFormula 0)
  obtain ⟨k1,h1⟩ := localWord_len (localFormula 1)
  obtain ⟨k2,h2⟩ := localWord_len (localFormula 2)
  obtain ⟨k3,h3⟩ := localWord_len (localFormula 3)
  let K := k0+k1+k2+k3
  refine ⟨K,fun base t => ?_⟩
  have step (k : ℕ) (h : k ≤ K) : k*(base.length+1) ≤ K*(base.length+1) := Nat.mul_le_mul_right _ h
  unfold completeWord sel
  split
  · exact (h3 base).trans (step k3 (by dsimp [K]; omega))
  · split
    · exact (h2 base).trans (step k2 (by dsimp [K]; omega))
    · split
      · exact (h1 base).trans (step k1 (by dsimp [K]; omega))
      · exact (h0 base).trans (step k0 (by dsimp [K]; omega))

theorem emitRaw_len : ∃ K, ∀ base a b c : Word,
    (emitRaw base a b c).length ≤ a.length+b.length+c.length+K*(base.length+1) := by
  obtain ⟨k,hk⟩ := completeWord_len
  refine ⟨k+12,fun base a b c => ?_⟩
  have hp := (keep_len (keep a b) c).trans (keep_len a b)
  have hq := keep_len b c
  have h1 := evenLit_len false (keep (keep a b) c)
  have h2 := evenLit_len false (keep b c)
  have h3 := evenLit_len false c
  have h4 := hk base (present (keep (keep a b) c) ++ present (keep b c) ++ present c)
  unfold emitRaw sel
  split
  · simp only [carry,List.length_append,Nat.add_mul]
    omega
  · exact Nat.zero_le _


def optional (w : Word) : List Word := if w = [] then [] else [w]

theorem optional_size (w : Word) : (optional w).length = (present w).length := by
  unfold optional present sel
  split <;> rfl

theorem optional_even (w : Word) :
    (optional w).flatMap (evenLit false) = evenLit false w := by
  unfold optional
  split
  · next h => rw [h]; rfl
  · simp

theorem keepWords_dedup (a b c : Word) :
    optional (keep (keep a b) c) ++ optional (keep b c) ++ optional c =
      (optional a ++ optional b ++ optional c).dedup := by
  by_cases ha : a = [] <;> by_cases hb : b = [] <;> by_cases hc : c = []
  all_goals
    by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
      simp_all [keep,optional,sel,bflag,List.dedup_cons,eq_comm]

theorem carry_eq (base a b c : Word) :
    carry base a b c =
      let ls := (optional a ++ optional b ++ optional c).dedup
      ls.flatMap (evenLit false) ++ localWord (localFormula (3-ls.length)) base := by
  have hwords := keepWords_dedup a b c
  let p := keep (keep a b) c
  let q := keep b c
  have h (w : Word) : (present w).length ≤ 1 := by
    unfold present sel
    split <;> decide
  have hsize : (present p ++ present q ++ present c).length ≤ 3 := by
    simp only [List.length_append]
    have h1 := h p
    have h2 := h q
    have h3 := h c
    omega
  unfold carry
  dsimp only
  change evenLit false p ++ evenLit false q ++ evenLit false c ++
      completeWord base (present p ++ present q ++ present c) = _
  rw [completeWord_spec _ _ hsize]
  rw [← hwords]
  simp only [List.flatMap_append,optional_even,List.length_append,optional_size]
  rfl

theorem conflict_cons (l r : Literal) :
    conflict (encodeLiteral l) (encodeLiteral r) ≠ [] ↔ l.1 = r.1 ∧ l.2 ≠ r.2 := by
  have ht (p : Literal) : (encodeLiteral p).tail.tail = vcode p.1 := by cases p; rfl
  have eqL := PEqualNP.Library.SearchHelpers.TwoSat.encodeLiteral_injective.eq_iff (a := l) (b := r)
  have eqV := vcode_injective.eq_iff (a := l.1) (b := r.1)
  unfold conflict
  rw [ht,ht]
  by_cases h1 : l.1 = r.1 <;> by_cases h2 : l.2 = r.2
  all_goals
    have hL : l = r ↔ l.1 = r.1 ∧ l.2 = r.2 := Prod.ext_iff
    simp [sel,bflag,eqL,eqV,hL,h1,h2]

theorem conflict_nil_left (w : Word) (h : w.tail.tail ≠ []) :
    conflict [] w = [] := by
  simp [conflict,sel,bflag,Ne.symm h]

theorem conflict_nil_right (w : Word) (h : w.tail.tail ≠ []) :
    conflict w [] = [] := by
  simp [conflict,sel,bflag,h]

theorem optional_lit (l : Literal) : optional (encodeLiteral l) = [encodeLiteral l] := by
  simp [optional,encodeLiteral]

theorem lit_tail_nonempty (l : Literal) : (encodeLiteral l).tail.tail ≠ [] := by
  cases l
  simp [encodeLiteral]

end PEqualNP.Outside.TernaryGadget
