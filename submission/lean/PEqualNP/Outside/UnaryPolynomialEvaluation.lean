import PEqualNP.Outside.UnaryRemainderMachine
import PEqualNP.Outside.BackdoorPathCore

namespace PEqualNP.Outside.UnaryPolynomialEvaluation

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (cut cut_cpt cut_eq)
open PEqualNP.Outside.UnaryRemainderMachine (rem rem_cpt rem_enc)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (q a r s p : Word) : Word := pairB q (pairB a (pairB r (pairB s p)))
def modulus (z : Word) : Word := (unpairB z).1
def point (z : Word) : Word := (unpairB (unpairB z).2).1
def payload (z : Word) : Word := (unpairB (unpairB z).2).2
def remaining (z : Word) : Word := (unpairB (payload z)).1
def accumulators (z : Word) : Word := (unpairB (payload z)).2
def residue (z : Word) : Word := (unpairB (accumulators z)).1
def power (z : Word) : Word := (unpairB (accumulators z)).2

def nextResidue (q r s p : Word) : Word :=
  cut q (sel (bflag (r.headD false)) s (rem (q, s ++ p)))

def nextPower (q a p : Word) : Word := cut q (rem (q, mulU a p))

def step (z : Word) : Word :=
  let q := modulus z
  let a := point z
  let r := remaining z
  let s := residue z
  let p := power z
  sel r z (pack q a r.tail (nextResidue q r s p) (nextPower q a p))

theorem residue_cpt : CPT residue :=
  cpt_unpairB1_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))

theorem remaining_cpt : CPT remaining :=
  cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)

theorem step_cpt : CPT step := by
  have hq : CPT modulus := cpt_unpairB1
  have ha : CPT point := cpt_unpairB1_1 cpt_unpairB2
  have hp : CPT power := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  have hs := residue_cpt
  have hr := remaining_cpt
  have hsum := cpt_comp (cpt_pairG hq (cpt_comp (cpt_pairG hs hp) cpt_append)) rem_cpt
  have hprod := cpt_comp (cpt_pairG hq (cpt_mulU2 ha hp)) rem_cpt
  have hns := cut_cpt hq (cpt_sel (cpt_comp hr cpt_firstF) hs hsum)
  have hnp := cut_cpt hq hprod
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 hq (cpt_pairB2 ha
    (cpt_pairB2 (cpt_tail1 hr) (cpt_pairB2 hns hnp))))) (fun _ => rfl)

def measure (z : Word) : ℕ := 3 * (modulus z).length + 4

theorem measure_step (z : Word) : measure (step z) ≤ measure z := by
  simp only [step, sel]
  split
  · rfl
  · simp [measure, modulus, pack, unpairB_pairB]

theorem step_size (z : Word) : (step z).length ≤ z.length + measure z := by
  have hq := unpairB_length z
  have ha := unpairB_length (unpairB z).2
  have hr := unpairB_length (payload z)
  have ht : (remaining z).tail.length ≤ (remaining z).length := by simp [List.length_tail]
  have hs : (nextResidue (modulus z) (remaining z) (residue z) (power z)).length ≤
      (modulus z).length := by simp [nextResidue, cut_eq]
  have hp : (nextPower (modulus z) (point z) (power z)).length ≤
      (modulus z).length := by simp [nextPower, cut_eq]
  simp only [step, sel]
  split
  · omega
  · simp only [pack, measure, pairB_length, modulus, point, remaining, payload] at *
    omega

theorem measure_bound (z : Word) : measure z ≤ 4 * z.length + 4 := by
  have h := unpairB_length z
  simp only [measure, modulus]
  omega

def start (z : Word) : Word :=
  pack (modulus z) (point z) (payload z) [] (rem (modulus z, [true]))

def evaluate (z : Word) : Word :=
  residue (step^[(payload z).length] (start z))

theorem evaluate_cpt : CPT evaluate := by
  have hq : CPT modulus := cpt_unpairB1
  have ha : CPT point := cpt_unpairB1_1 cpt_unpairB2
  have hr : CPT payload := cpt_unpairB2_1 cpt_unpairB2
  have hpow := cpt_comp (cpt_pairG hq (cpt_const [true])) rem_cpt
  have hs : CPT start := cptl
    (cpt_pairB2 hq (cpt_pairB2 ha (cpt_pairB2 hr (cpt_pairB2 (cpt_const []) hpow)))) (fun _ => rfl)
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime_measure step m measure 4 measure_step step_size measure_bound
  exact cptl (cpt_comp (cpt_comp (cpt_pairG hs hr) loop) residue_cpt) (fun _ => rfl)

def natEval (a : ℕ) : Word → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + a * natEval a bs

theorem cut_un (q : Word) (j : ℕ) (h : j ≤ q.length) : cut q (un j) = un j := by
  rw [cut_eq, List.take_of_length_le]
  simpa only [un_length] using h


theorem run (q a r : Word) (hq : 0 < q.length) (s p : ℕ)
    (hs : s < q.length) :
    residue (step^[r.length] (pack q a r (un s) (un p))) =
      un ((s + p * natEval a.length r) % q.length) := by
  induction r generalizing s p with
  | nil => simp [pack, residue, accumulators, payload, unpairB_pairB, natEval, Nat.mod_eq_of_lt hs]
  | cons b bs ih =>
    let s' := (s + p * (if b then 1 else 0)) % q.length
    let p' := (a.length * p) % q.length
    have hs' : s' < q.length := Nat.mod_lt _ hq
    have hp' : p' < q.length := Nat.mod_lt _ hq
    have hn : nextResidue q (b :: bs) (un s) (un p) = un s' := by
      cases b
      · simp [nextResidue, bflag, sel, s', Nat.mod_eq_of_lt hs, cut_un q s hs.le]
      · simp only [nextResidue, List.headD_cons, bflag, sel, if_false, rem_enc,
          List.length_append, un_length, s', if_true, mul_one]
        exact cut_un q _ (Nat.mod_lt _ hq).le
    have hm : nextPower q a (un p) = un p' := by
      simp [nextPower, rem_enc, mulU, un_length, p', cut_un q _ hp'.le]
    have he : step (pack q a (b :: bs) (un s) (un p)) = pack q a bs (un s') (un p') := by
      simp [step, pack, modulus, point, remaining, residue, power, accumulators, payload, unpairB_pairB, sel, hn, hm]
    rw [List.length_cons, Function.iterate_succ_apply, he, ih s' p' hs']
    congr 1
    change (s' + p' * natEval a.length bs) % q.length = _
    refine ((Nat.mod_modEq _ _).add ((Nat.mod_modEq _ _).mul
      (Nat.ModEq.refl (natEval a.length bs)))).trans ?_
    change _ % q.length = _ % q.length
    congr 1
    simp only [natEval]
    ring

theorem evaluate_correct (q a r : Word) (hq : 0 < q.length) :
    evaluate (pairB q (pairB a r)) = un (natEval a.length r % q.length) := by
  simp only [evaluate, start, modulus, point, payload, unpairB_pairB, rem_enc, List.length_cons,
    List.length_nil, zero_add]
  change residue (step^[r.length] (pack q a r (un 0) (un (1 % q.length)))) = _
  rw [run q a r hq 0 _ hq, zero_add]
  congr 1
  have h : Nat.ModEq q.length (1 % q.length * natEval a.length r) (natEval a.length r) := by
    simpa only [one_mul] using
      ((Nat.mod_modEq 1 q.length).mul (Nat.ModEq.refl (natEval a.length r)))
  exact h

theorem natEval_ofFn (a : ℕ) {n : ℕ} (u : Fin n → Bool) :
    natEval a (List.ofFn u) = ∑ i : Fin n, (if u i then 1 else 0) * a ^ i.val := by
  induction n with
  | zero => simp [natEval]
  | succ n ih =>
    rw [List.ofFn_succ, natEval, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

end PEqualNP.Outside.UnaryPolynomialEvaluation

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.UnaryPolynomialEvaluation

theorem PEqualNP.Outside.UnaryPolynomialEvaluation :
    ∃ eval : List Bool → List Bool,
      ComputableInPolyTime (fun w => w) (fun w => w) eval ∧
      ∀ (q a : List Bool) (n : ℕ) (u : Fin n → Bool), 0 < q.length →
        eval (List.replicate q.length true ++ false ::
          (q ++ (List.replicate a.length true ++ false :: (a ++ List.ofFn u)))) =
          List.replicate ((∑ i : Fin n, (if u i then 1 else 0) * a.length ^ i.val) % q.length) true := by
  refine ⟨evaluate, evaluate_cpt, ?_⟩
  intro q a n u hq
  change evaluate (pairB q (pairB a (List.ofFn u))) = _
  rw [evaluate_correct q a _ hq, natEval_ofFn]
  rfl
