import PEqualNP.Outside.RecordPrefixQueries

namespace PEqualNP.Outside.RecordAttachQuery

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.RecordPrefixQueries (wire_append)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (x r out : Word) : Word := pairB x (pairB r out)
def source (z : Word) : Word := (unpairB z).1
def rest (z : Word) : Word := (unpairB (unpairB z).2).1
def output (z : Word) : Word := (unpairB (unpairB z).2).2

def step (z : Word) : Word :=
  let x := source z
  let r := rest z
  let next := unpairB r
  sel r z (pack x next.2 (output z ++ pairB (pairB x next.1) []))

theorem step_cpt : CPT step := by
  have hx : CPT source := cpt_unpairB1
  have hr : CPT rest := cpt_unpairB1_1 cpt_unpairB2
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  have hword := cpt_pairB2 (cpt_pairB2 hx (cpt_unpairB1_1 hr)) (cpt_const [])
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 hx
    (cpt_pairB2 (cpt_unpairB2_1 hr) (cpt_app2 ho hword)))) (fun _ => rfl)

def measure (z : Word) : ℕ := 4 * (source z).length + 5

theorem step_size (z : Word) : (step z).length ≤ z.length + measure z := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have h3 := unpairB_length (rest z)
  simp only [step, sel]
  split
  · omega
  · simp only [pack,pairB_length,List.length_append,List.length_nil,measure,source,rest,output] at *
    omega

theorem measure_step (z : Word) : measure (step z) ≤ measure z := by
  simp only [measure, step, sel]
  split
  · omega
  · simp [pack,source,unpairB_pairB]

def attach (q : Word × Word) : Word := output (step^[q.2.length] (pack q.1 q.2 []))

theorem attach_cpt : ComputableInPolyTime encodePair (fun x : Word => x) attach := by
  obtain ⟨m⟩ := step_cpt
  have hlo := Iter.iter_polyTime_measure step m measure 9 measure_step step_size (by
    intro z
    have h := unpairB_length z
    unfold measure source
    omega)
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 q.2 []) :=
    cptl (cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const []))))
      (fun q => by simp [pack, unpairB_pairB])
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pairG hs cpt_snd) hlo) ho) (fun _ => rfl)

theorem step_enc (x r : Word) (rs acc : List Word) :
    step (pack x (wire (r :: rs)) (wire acc)) =
      pack x (wire rs) (wire (acc ++ [pairB x r])) := by
  have hn : pairB r (wire rs) ≠ [] := by simp [pairB]
  simp [step, pack, source, rest, output, wire, unpairB_pairB, sel, hn, wire_append]

theorem scan (x : Word) (rs acc : List Word) :
    step^[rs.length] (pack x (wire rs) (wire acc)) =
      pack x [] (wire (acc ++ rs.map (pairB x))) := by
  induction rs generalizing acc with
  | nil => simp [wire]
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, step_enc, ih]
    simp [List.append_assoc]

theorem attach_enc (x : Word) (rs : List Word) : attach (x,wire rs) = wire (rs.map (pairB x)) := by
  have hn := wire_len rs
  have hf : step (pack x [] (wire (rs.map (pairB x)))) = pack x [] (wire (rs.map (pairB x))) := by
    simp [step, pack, rest, sel, unpairB_pairB]
  have hs := scan x rs []
  simp only [wire,List.nil_append] at hs
  unfold attach
  simp only
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, hs, Function.iterate_fixed hf]
  simp [output,pack,unpairB_pairB]

end PEqualNP.Outside.RecordAttachQuery
