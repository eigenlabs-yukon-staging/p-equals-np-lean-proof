import PEqualNP.Outside.RecordPairScan

namespace PEqualNP.Outside.RecordPrefixQueries

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_eq cut_cpt)
open PEqualNP.Outside.RecordPairScan (wire wire_len rec_len)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (x all rest current output : Word) : Word :=
  pairB x (pairB all (pairB rest (pairB current output)))

def source (z : Word) : Word := (unpairB z).1
def t1 (z : Word) : Word := (unpairB z).2
def archive (z : Word) : Word := (unpairB (t1 z)).1
def t2 (z : Word) : Word := (unpairB (t1 z)).2
def remaining (z : Word) : Word := (unpairB (t2 z)).1
def t3 (z : Word) : Word := (unpairB (t2 z)).2
def middle (z : Word) : Word := (unpairB (t3 z)).1
def output (z : Word) : Word := (unpairB (t3 z)).2

def step (z : Word) : Word :=
  let x := source z
  let all := archive z
  let r := remaining z
  let head := cut all (unpairB r).1
  let tail := (unpairB r).2
  let curr := cut all (middle z ++ pairB head [])
  let more := pairB (pairB x curr) []
  sel r z (pack x all tail curr (output z ++ more))

theorem step_cpt : CPT step := by
  have hx : CPT source := cpt_unpairB1
  have h1 : CPT t1 := cpt_unpairB2
  have ha : CPT archive := cpt_unpairB1_1 h1
  have h2 : CPT t2 := cpt_unpairB2_1 h1
  have hr : CPT remaining := cpt_unpairB1_1 h2
  have h3 : CPT t3 := cpt_unpairB2_1 h2
  have hc : CPT middle := cpt_unpairB1_1 h3
  have ho : CPT output := cpt_unpairB2_1 h3
  have hhead := cut_cpt ha (cpt_unpairB1_1 hr)
  have hnext := cut_cpt ha (cpt_app2 hc (cpt_pairB2 hhead (cpt_const [])))
  have hout := cpt_app2 ho (cpt_pairB2 (cpt_pairB2 hx hnext) (cpt_const []))
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 hx (cpt_pairB2 ha
    (cpt_pairB2 (cpt_unpairB2_1 hr) (cpt_pairB2 hnext hout))))) (fun _ => rfl)

def measure (z : Word) : ℕ := 4 * (source z).length + 4 * (archive z).length + 7

theorem measure_step (z : Word) : measure (step z) ≤ measure z := by
  unfold measure
  simp only [step, sel]
  split
  · exact le_rfl
  · simp [pack, source, archive, t1, unpairB_pairB]

theorem step_bound (z : Word) : (step z).length ≤ z.length + measure z := by
  have h0 := unpairB_length z
  have h1 := unpairB_length (t1 z)
  have h2 := unpairB_length (t2 z)
  have h3 := unpairB_length (t3 z)
  have hr := unpairB_length (remaining z)
  have hc (w : Word) : (cut (archive z) w).length ≤ (archive z).length := by
    simp [cut_eq, List.length_take]
  have hn := hc (middle z ++ pairB (cut (archive z) (unpairB (remaining z)).1) [])
  simp only [step, sel]
  split
  · omega
  · simp only [measure, pack, pairB_length, List.length_append, List.length_nil,
      source, archive, remaining, output, t1, t2, t3] at *
    omega

def batch (q : Word × Word) : Word :=
  output (step^[q.2.length] (pack q.1 q.2 q.2 [] []))

theorem batch_cpt : ComputableInPolyTime encodePair (fun x : Word => x) batch := by
  obtain ⟨m⟩ := step_cpt
  have hlo := Iter.iter_polyTime_measure step m measure 15 measure_step step_bound (by
    intro z
    have h0 := unpairB_length z
    have h1 := unpairB_length (t1 z)
    simp only [measure, source, archive, t1] at *
    omega)
  have hseed : ComputableInPolyTime encodePair (fun w : Word => w)
      (fun q : Word × Word => pack q.1 q.2 q.2 [] []) :=
    cptl (cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2
      (cpt_pairB2 cpt_unpairB2 (cpt_const (pairB [] [])))))) (fun _ => by simp [pack, unpairB_pairB])
  have ho : CPT output := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact cptl (cpt_comp (cpt_comp (cpt_pairG hseed cpt_snd) hlo) ho) (fun _ => rfl)

theorem wire_append (a b : List Word) : wire (a ++ b) = wire a ++ wire b := by
  induction a with
  | nil => rfl
  | cons r a ih =>
    rw [List.cons_append, wire, wire, ih]
    simp [pairB, List.append_assoc]

def listFrom (x : Word) (current : List Word) : List Word → List Word
  | [] => []
  | r :: rs => pairB x (wire (current ++ [r])) :: listFrom x (current ++ [r]) rs

def state (x : Word) (all r curr out : List Word) : Word :=
  pack x (wire all) (wire r) (wire curr) (wire out)

theorem step_enc (x : Word) (all curr : List Word) (r : Word) (rs acc : List Word)
    (h : all = curr ++ r :: rs) :
    step (state x all (r :: rs) curr acc) =
      state x all rs (curr ++ [r]) (acc ++ [pairB x (wire (curr ++ [r]))]) := by
  have hr : r.length ≤ (wire all).length := rec_len (by simp [h])
  have hp : (wire (curr ++ [r])).length ≤ (wire all).length := by
    have he : all = (curr ++ [r]) ++ rs := by simp [h, List.append_assoc]
    rw [he, wire_append (curr ++ [r]) rs, List.length_append]
    omega
  have hn : pairB r (wire rs) ≠ [] := by simp [pairB]
  have ha := wire_append curr [r]
  have hb := wire_append acc [pairB x (wire (curr ++ [r]))]
  change wire (curr ++ [r]) = wire curr ++ pairB r [] at ha
  change wire (acc ++ [pairB x (wire (curr ++ [r]))]) =
    wire acc ++ pairB (pairB x (wire (curr ++ [r]))) [] at hb
  simp only [step, state, pack, source, archive, remaining, middle, output, t1, t2, t3,
    wire, unpairB_pairB, sel, hn, ite_false, cut_eq, List.take_of_length_le hr, ← ha,
    List.take_of_length_le hp, ← hb]

theorem step_halt (x : Word) (all pref out : List Word) :
    step (state x all [] pref out) = state x all [] pref out := by
  simp [state, step, pack, remaining, t2, t1, wire, unpairB_pairB, sel]

theorem scan (x : Word) (all curr rs acc : List Word) (h : all = curr ++ rs) :
    step^[rs.length] (state x all rs curr acc) = state x all [] (curr ++ rs) (acc ++ listFrom x curr rs) := by
  induction rs generalizing curr acc with
  | nil => simp [listFrom]
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, step_enc x all curr r rs acc h]
    have hh : all = (curr ++ [r]) ++ rs := by simp [h, List.append_assoc]
    rw [ih _ _ hh]
    simp [listFrom, List.append_assoc]

theorem batch_enc (x : Word) (rs : List Word) :
    batch (x, wire rs) = wire (listFrom x [] rs) := by
  have h := wire_len rs
  unfold batch
  change output (step^[(wire rs).length] (state x rs rs [] [])) = _
  rw [← Nat.sub_add_cancel h, Function.iterate_add_apply, scan x rs [] rs [] (by simp),
    Function.iterate_fixed (step_halt _ _ _ _)]
  simp [output, state, pack, t1, t2, t3, unpairB_pairB]

end PEqualNP.Outside.RecordPrefixQueries
