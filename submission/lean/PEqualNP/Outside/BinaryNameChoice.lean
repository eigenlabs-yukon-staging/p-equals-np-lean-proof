import PEqualNP.Outside.AlternatingNameScan
import PEqualNP.Outside.FirstWideClause

namespace PEqualNP.Outside.BinaryNameChoice

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.AlternatingNameScan (Word sieve sieve_cpt sieve_length alternating sieve_codes)
open PEqualNP.Outside.FirstWideClause (names)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (z : Word) : Word :=
  let b := (unpairB z).1
  let q := (unpairB z).2
  sel b z (pairB b.tail (sieve (q, sel (bflag (b.headD false)) [true] [])))

theorem step_cpt : CPT step := by
  have hb := cpt_unpairB1
  have hf := cpt_sel (cpt_comp hb cpt_firstF) (cpt_const [true]) (cpt_const [])
  have hread := cpt_comp (cpt_pair cpt_unpairB2 hf) sieve_cpt
  exact cptl (cpt_sel hb cpt_id (cpt_pairB2 (cpt_tail1 hb) hread)) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 1 := by
  have h := unpairB_length z
  have hp := sieve_length ((unpairB z).2, sel (bflag ((unpairB z).1.headD false)) [true] [])
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length, List.length_tail]
    unfold sel at hp
    simp only [Prod.fst] at hp
    omega

def pickRaw (q : Word × Word) : Word :=
  headI (unpairB (step^[q.2.length] (pairB q.2 q.1))).2

theorem pickRaw_cpt : ComputableInPolyTime encodePair (fun x : Word => x) pickRaw := by
  obtain ⟨m⟩ := step_cpt
  have hLoop := Iter.iter_polyTime step m 1 step_length
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pairB q.2 q.1) := by
    have h := cpt_comp cpt_swap cpt_pairB
    exact h
  have h := cpt_comp (cpt_comp (cpt_pairG hs cpt_snd) hLoop) (cpt_comp cpt_unpairB2 cpt_headI)
  exact h

def choose (q : Word × Word) : Word :=
  sel (pickRaw q) (headI q.1) (pickRaw q)

theorem choose_cpt : ComputableInPolyTime encodePair (fun x : Word => x) choose := by
  have h₁ := cpt_comp cpt_fst cpt_headI
  have h := cpt_comp (cpt_pairG pickRaw_cpt h₁) cpt_pairB
  have hS := cpt_sel cpt_unpairB1 cpt_unpairB2 cpt_unpairB1
  exact cptl (cpt_comp h hS) (fun q => by simp [choose, unpairB_pairB])

def binaryValue : Word → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * binaryValue bs

def lowDigits : ℕ → ℕ → Word
  | 0, _ => []
  | d + 1, i => decide (i % 2 = 1) :: lowDigits d (i / 2)

theorem lowDigits_length (d i : ℕ) : (lowDigits d i).length = d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => simp [lowDigits, ih]

theorem binaryValue_lowDigits (d i : ℕ) (h : i < 2 ^ d) : binaryValue (lowDigits d i) = i := by
  induction d generalizing i with
  | zero =>
    simp at h
    subst i
    rfl
  | succ d ih =>
    have h' : i / 2 < 2 ^ d := by
      rw [pow_succ] at h
      omega
    have hm : i % 2 = (if i % 2 = 1 then 1 else 0) := by
      split <;> omega
    simp only [lowDigits, binaryValue, decide_eq_true_eq, ih _ h']
    omega

def resolve {α : Type} : Word → List α → List α
  | [], xs => xs
  | b :: bs, xs => resolve bs (alternating (!b) xs)

theorem alternating_get {α : Type} (xs : List α) (b : Bool) (j : ℕ) :
    (alternating (!b) xs)[j]? = xs[2 * j + (if b then 1 else 0)]? := by
  induction xs using List.twoStepInduction generalizing j b with
  | nil => rfl
  | singleton a =>
    cases b <;> cases j <;> simp [alternating, Nat.mul_add]
  | cons_cons a c xs ih =>
    cases j with
    | zero => cases b <;> rfl
    | succ j =>
      cases b with
      | false =>
        change (alternating true xs)[j]? = (a :: c :: xs)[2 * (j + 1) + 0]?
        rw [show 2 * (j + 1) + 0 = (2 * j) + 2 from by omega]
        exact ih false j
      | true =>
        change (alternating false xs)[j]? = (a :: c :: xs)[2 * (j + 1) + 1]?
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by omega]
        exact ih true j

theorem resolve_get {α : Type} (bits : Word) (xs : List α) (j : ℕ) :
    (resolve bits xs)[j]? = xs[2 ^ bits.length * j + binaryValue bits]? := by
  induction bits generalizing xs j with
  | nil => simp [resolve, binaryValue]
  | cons b bs ih =>
    rw [resolve, ih, alternating_get]
    simp only [List.length_cons, pow_succ, binaryValue]
    congr 1
    ring

theorem run_codes (bits : Word) (vs : List ℕ) :
    step^[bits.length] (pairB bits (vs.flatMap vcode)) =
      pairB [] ((resolve bits vs).flatMap vcode) := by
  induction bits generalizing vs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have h : step (pairB (b :: bs) (vs.flatMap vcode)) =
        pairB bs ((alternating (!b) vs).flatMap vcode) := by
      cases b
      · have h := sieve_codes vs true
        simp [bflag] at h
        simp [step, sel, bflag, unpairB_pairB, h]
      · have h := sieve_codes vs false
        simp [bflag] at h
        simp [step, sel, bflag, unpairB_pairB, h]
    rw [h]
    exact ih _

theorem pickRaw_names (c : Clause) (bits : Word) :
    pickRaw (names c, bits) = ((c[binaryValue bits]?.map (fun l => vcode l.1))).getD [] := by
  simp only [pickRaw, names, Prod.fst, Prod.snd, run_codes, unpairB_pairB]
  have h := resolve_get bits (c.map Prod.fst) 0
  simp only [Nat.mul_zero, Nat.zero_add, List.getElem?_map] at h
  cases he : resolve bits (c.map Prod.fst) with
  | nil =>
    rw [he] at h
    cases hx : c[binaryValue bits]? <;> simp [hx] at h
    simp [he, hx, headI]
  | cons i xs =>
    rw [he] at h
    cases hx : c[binaryValue bits]? with
    | none => simp [hx] at h
    | some l =>
      have hi : i = l.1 := by simpa [hx] using h
      simp [he, hx, List.flatMap_cons, headI_vcode, hi]

theorem choose_encoded (c : Clause) (bits : Word) (j : ℕ) (l : Literal)
    (hj : binaryValue bits = j) (hl : c[j]? = some l) :
    choose (names c, bits) = vcode l.1 := by
  simp [choose, pickRaw_names, hj, hl, sel, vcode_ne_nil]

theorem choose_member (c : Clause) (bits : Word) (hn : c ≠ []) :
    ∃ l ∈ c, choose (names c, bits) = vcode l.1 := by
  cases h : c[binaryValue bits]? with
  | none =>
    obtain ⟨l, cs, rfl⟩ := List.exists_cons_of_ne_nil hn
    refine ⟨l, by simp, ?_⟩
    rw [choose, pickRaw_names, h]
    simp [sel, names, List.flatMap_cons, headI_vcode]
  | some l =>
    exact ⟨l, List.mem_of_getElem? h, choose_encoded c bits (binaryValue bits) l rfl h⟩

end PEqualNP.Outside.BinaryNameChoice
