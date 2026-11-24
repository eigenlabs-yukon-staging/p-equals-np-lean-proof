import PEqualNP.Outside.BackdoorPathCore
import PEqualNP.Outside.FirstWideCollector

namespace PEqualNP.Outside.RecordPairScan

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_cpt cut_eq)
open PEqualNP.Outside.FirstWideCollector (pack pack_length)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def wire : List Word → Word
  | [] => []
  | a :: as => pairB a (wire as)

theorem wire_len (xs : List Word) : xs.length ≤ (wire xs).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [wire, pairB_length, List.length_cons]; omega

theorem rec_len {xs : List Word} {a : Word} (ha : a ∈ xs) : a.length ≤ (wire xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rw [wire, pairB_length]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h := ih ha
      omega

def original (z : Word) : Word := (unpairB z).1
def outer (z : Word) : Word := (unpairB (unpairB z).2).1
def inner (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def output (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2

def step (emit : Word × Word → Word) (z : Word) : Word :=
  let x := original z
  let o := outer z
  let i := inner z
  let acc := output z
  let advance := pack x (unpairB o).2 x acc
  let appendWord := emit (cut x (unpairB o).1, cut x (unpairB i).1)
  let more := pack x o (unpairB i).2 (acc ++ appendWord)
  sel o z (sel i advance more)

theorem step_cpt (emit : Word × Word → Word)
    (he : ComputableInPolyTime encodePair (fun x : Word => x) emit) : CPT (step emit) := by
  have hx : CPT original := cpt_unpairB1
  have ho : CPT outer := cpt_unpairB1_1 cpt_unpairB2
  have q := cpt_unpairB2_1 cpt_unpairB2
  have hi : CPT inner := cpt_unpairB1_1 q
  have ha : CPT output := cpt_unpairB2_1 q
  have hnext := cpt_pairB2 hx (cpt_pairB2 (cpt_unpairB2_1 ho) (cpt_pairB2 hx ha))
  have hpair := cpt_pair (cut_cpt hx (cpt_unpairB1_1 ho)) (cut_cpt hx (cpt_unpairB1_1 hi))
  have hword := cpt_comp (g := emit) hpair he
  have hmore := cpt_pairB2 hx (cpt_pairB2 ho (cpt_pairB2 (cpt_unpairB2_1 hi) (cpt_app2 ha hword)))
  exact cptl (cpt_sel ho cpt_id (cpt_sel hi hnext hmore)) (fun _ => rfl)

def measure (k c : ℕ) (z : Word) : ℕ := (2 * k + 2) * (original z).length + c + 7

theorem original_step (emit : Word × Word → Word) (z : Word) :
    original (step emit z) = original z := by
  simp only [step, sel]
  split
  · rfl
  · split <;> simp [original, pack, unpairB_pairB]

theorem step_bound (emit : Word × Word → Word) (k c : ℕ)
    (he : ∀ a b : Word, (emit (a,b)).length ≤ k * a.length + k * b.length + c) (z : Word) :
    (step emit z).length ≤ z.length + measure k c z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  have ho := unpairB_length (outer z)
  have hi := unpairB_length (inner z)
  have hcut (r : Word) : (cut (original z) (unpairB r).1).length ≤ (original z).length := by
    simp [cut_eq, List.length_take]
  have hb := he (cut (original z) (unpairB (outer z)).1) (cut (original z) (unpairB (inner z)).1)
  have hl := Nat.mul_le_mul_left k (hcut (outer z))
  have hr := Nat.mul_le_mul_left k (hcut (inner z))
  unfold measure
  rw [Nat.add_mul, Nat.mul_assoc]
  simp only [step, sel]
  split
  · omega
  · split <;> simp only [pack_length, List.length_append]
    · simp only [original, outer, inner, output] at *
      omega
    · simp only [original, outer, inner, output] at *
      omega

def ready (x o a : Word) : Word := pack x o x a

def compile (emit : Word × Word → Word) (x : Word) : Word :=
  output ((step emit)^[x.length * x.length + x.length] (ready x x []))

theorem compile_cpt (emit : Word × Word → Word)
    (he : ComputableInPolyTime encodePair (fun x : Word => x) emit)
    (k c : ℕ) (hsize : ∀ a b : Word, (emit (a,b)).length ≤ k * a.length + k * b.length + c) :
    CPT (compile emit) := by
  obtain ⟨m⟩ := step_cpt emit he
  have hlo := Iter.iter_polyTime_measure (step emit) m (measure k c) (2 * k + 2 + c + 7)
    (by intro z; simp [measure, original_step]) (step_bound emit k c hsize) (by
      intro z
      have h := unpairB_length z
      simp only [measure, original]
      have hle : (2 * k + 2) * (unpairB z).1.length ≤ (2 * k + 2) * z.length :=
        Nat.mul_le_mul_left _ (by omega)
      have hcoef : (2 * k + 2) * z.length ≤ (2 * k + 2 + c + 7) * z.length :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  have hs : CPT (fun x => ready x x []) :=
    cpt_pairB2 cpt_id (cpt_pairB2 cpt_id (cpt_pairB2 cpt_id (cpt_const [])))
  have hclock := cpt_app2 (cpt_mulU2 cpt_id cpt_id) cpt_id
  have hout : CPT output := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  exact cptl (cpt_comp (cpt_comp (cpt_pair hs hclock) hlo) hout) (fun x => by
    simp [compile, mulU, un_length])

private theorem step_pair (emit : Word × Word → Word) (x a b o i acc : Word)
    (ha : a.length ≤ x.length) (hb : b.length ≤ x.length) :
    step emit (pack x (pairB a o) (pairB b i) acc) =
      pack x (pairB a o) i (acc ++ emit (a,b)) := by
  have hna : pairB a o ≠ [] := by simp [pairB]
  have hnb : pairB b i ≠ [] := by simp [pairB]
  simp [step, original, outer, inner, output, pack, unpairB_pairB, sel, hna, hnb,
    cut_eq, List.take_of_length_le ha, List.take_of_length_le hb]

private theorem step_advance (emit : Word × Word → Word) (x a o acc : Word) :
    step emit (pack x (pairB a o) [] acc) = ready x o acc := by
  have hna : pairB a o ≠ [] := by simp [pairB]
  simp [step, original, outer, inner, output, ready, pack, unpairB_pairB, sel, hna]

private theorem step_halt (emit : Word × Word → Word) (x acc : Word) :
    step emit (ready x [] acc) = ready x [] acc := by
  simp [step, original, outer, inner, output, ready, pack, unpairB_pairB, sel]

theorem scan_inner (emit : Word × Word → Word) (x a o acc : Word)
    (ys : List Word) (ha : a.length ≤ x.length)
    (hb : ∀ b ∈ ys, b.length ≤ x.length) :
    (step emit)^[ys.length] (pack x (pairB a o) (wire ys) acc) =
      pack x (pairB a o) [] (acc ++ ys.flatMap fun b => emit (a,b)) := by
  induction ys generalizing acc with
  | nil => simp [wire]
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, wire,
      step_pair emit x a b o (wire bs) acc ha (hb b (by simp))]
    rw [ih _ (fun d hd => hb d (by simp [hd])), List.flatMap_cons, List.append_assoc]

theorem scan_outer (emit : Word × Word → Word) (xs os : List Word) (acc : Word)
    (hos : ∀ a ∈ os, a.length ≤ (wire xs).length) :
    (step emit)^[(xs.length + 1) * os.length] (ready (wire xs) (wire os) acc) =
      ready (wire xs) [] (acc ++ os.flatMap (fun a => xs.flatMap fun b => emit (a,b))) := by
  induction os generalizing acc with
  | nil => simp [wire]
  | cons a os ih =>
    rw [List.length_cons, Nat.mul_succ, Function.iterate_add_apply, Function.iterate_succ_apply',
      ready, wire, scan_inner emit (wire xs) a (wire os) acc xs (hos a (by simp)) (fun b hb => rec_len hb),
      step_advance, ih _ (fun b hb => hos b (by simp [hb])), List.flatMap_cons, List.append_assoc]

theorem compile_enc (emit : Word × Word → Word) (xs : List Word) :
    compile emit (wire xs) = xs.flatMap (fun a => xs.flatMap fun b => emit (a,b)) := by
  have hl := wire_len xs
  have hb : (xs.length + 1) * xs.length ≤ (wire xs).length * (wire xs).length + (wire xs).length := by
    calc
      _ ≤ ((wire xs).length + 1) * (wire xs).length :=
        Nat.mul_le_mul (Nat.add_le_add_right hl 1) hl
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]
  unfold compile
  rw [← Nat.sub_add_cancel hb, Function.iterate_add_apply, scan_outer emit xs xs [] (fun a ha => rec_len ha),
    Function.iterate_fixed (step_halt emit _ _)]
  simp [output, ready, pack, unpairB_pairB]

end PEqualNP.Outside.RecordPairScan
