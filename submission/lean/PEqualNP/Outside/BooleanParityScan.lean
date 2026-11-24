import PEqualNP.Outside.SatCodePrimitives
import PEqualNP.Library.Universal.Padding

namespace PEqualNP.Outside.BooleanParityScan

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (a b f : Word) : Word := pairB a (pairB b f)

def left (z : Word) : Word := (unpairB z).1
def right (z : Word) : Word := (unpairB (unpairB z).2).1
def flag (z : Word) : Word := (unpairB (unpairB z).2).2

def step (z : Word) : Word :=
  let a := left z
  let b := right z
  let f := flag z
  let next := sel (bflag (a.headD false)) f (sel (bflag (b.headD false)) f (sel f [true] []))
  sel a z (pack a.tail b.tail next)

theorem step_cpt : CPT step := by
  have ha : CPT left := cpt_unpairB1
  have hb : CPT right := cpt_unpairB1_1 cpt_unpairB2
  have hf : CPT flag := cpt_unpairB2_1 cpt_unpairB2
  have hha := cpt_comp ha cpt_firstF
  have hhb := cpt_comp hb cpt_firstF
  have hflip := cpt_sel hf (cpt_const [true]) (cpt_const [])
  have hn := cpt_sel hha hf (cpt_sel hhb hf hflip)
  exact cptl (cpt_sel ha cpt_id (cpt_pairB2 (cpt_tail1 ha)
    (cpt_pairB2 (cpt_tail1 hb) hn))) (fun _ => rfl)

theorem step_bound (z : Word) : (step z).length ≤ z.length + 3 := by
  have hp := unpairB_length z
  have hq := unpairB_length (unpairB z).2
  have ha : (left z).tail.length ≤ (left z).length := by simp [List.length_tail]
  have hb : (right z).tail.length ≤ (right z).length := by simp [List.length_tail]
  have hn : (sel (bflag ((left z).headD false)) (flag z)
      (sel (bflag ((right z).headD false)) (flag z) (sel (flag z) [true] []))).length ≤
      (flag z).length + 1 := by
    unfold sel
    split
    · omega
    · split
      · omega
      · split <;> simp
  change (if left z = [] then z else pack (left z).tail (right z).tail
    (sel (bflag ((left z).headD false)) (flag z)
      (sel (bflag ((right z).headD false)) (flag z) (sel (flag z) [true] [])))).length ≤ _
  split
  · omega
  · simp only [pack, pairB_length, left, right, flag] at *
    omega

def parityWord (q : Word × Word) : Word :=
  flag (step^[q.1.length] (pack q.1 q.2 []))

theorem parityWord_cpt : ComputableInPolyTime encodePair (fun w : Word => w) parityWord := by
  obtain ⟨m⟩ := step_cpt
  have hp : ComputableInPolyTime encodePair (fun x : Word => x) (fun q : Word × Word => pack q.1 q.2 []) :=
    cptl (cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const []))))
      (fun _ => by simp [pack, unpairB_pairB])
  have loop := Iter.iter_polyTime step m 3 step_bound
  have hf : CPT flag := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pairG hp cpt_fst) loop) hf) (fun _ => rfl)

def parity : Word → Word → Bool → Bool
  | [], _, init => init
  | a :: as, bs, init => parity as bs.tail (xor init (a && bs.headD false))

theorem step_cons (a : Bool) (as bs : Word) (init : Bool) :
    step (pack (a :: as) bs (bflag init)) =
      pack as bs.tail (bflag (xor init (a && bs.headD false))) := by
  cases a <;> cases init <;> rcases bs with _ | ⟨b, bs⟩ <;>
    simp [step, pack, left, right, flag, bflag, sel, unpairB_pairB] <;>
    cases b <;> simp [bflag, sel]

theorem run (as bs : Word) (init : Bool) :
    flag (step^[as.length] (pack as bs (bflag init))) = bflag (parity as bs init) := by
  induction as generalizing bs init with
  | nil => simp [pack, flag, parity, unpairB_pairB]
  | cons a as ih =>
    rw [List.length_cons, Function.iterate_succ_apply, step_cons]
    exact ih _ _

theorem parityWord_correct (as bs : Word) : parityWord (as, bs) = bflag (parity as bs false) :=
  run as bs false

end PEqualNP.Outside.BooleanParityScan
