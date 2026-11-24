import PEqualNP.Outside.RecordPrefixQueries
import PEqualNP.Library.L055

namespace PEqualNP.Outside.RecordBlockSplit

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_cpt cut_eq)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordPrefixQueries (wire_append)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def pack (c r out : Word) : Word := pairB c (pairB r out)
def clock (z : Word) : Word := (unpairB z).1
def rest (z : Word) : Word := (unpairB (unpairB z).2).1
def output (z : Word) : Word := (unpairB (unpairB z).2).2

def skip (c r : Word) : Word := r.drop c.length

private theorem iter_tail (n : ℕ) (s : Word) : List.tail^[n] s = s.drop n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases s <;> simp

theorem skip_cpt {c r : Word → Word} (hc : CPT c) (hr : CPT r) : CPT (fun z => skip (c z) (r z)) :=
  cptl (cpt_iterLen cpt_tail (by intro w; simp [List.length_tail]) hc hr) (fun _ => iter_tail _ _)

def step (z : Word) : Word :=
  let c := clock z
  let r := rest z
  let more := pairB (cut c r) []
  sel c z (sel r z (pack c (skip c r) (output z ++ more)))

theorem step_cpt : CPT step := by
  have hc : CPT clock := cpt_unpairB1
  have hr : CPT rest := cpt_unpairB1_1 cpt_unpairB2
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  have hb := cpt_pairB2 (cut_cpt hc hr) (cpt_const [])
  exact cptl (cpt_sel hc cpt_id (cpt_sel hr cpt_id
    (cpt_pairB2 hc (cpt_pairB2 (skip_cpt hc hr) (cpt_app2 ho hb))))) (fun _ => rfl)

theorem step_bound (z : Word) : (step z).length ≤ z.length + 3 := by
  have h0 := unpairB_length z
  have h1 := unpairB_length (unpairB z).2
  have h := congrArg List.length (List.take_append_drop (clock z).length (rest z))
  simp only [List.length_append, ← cut_eq] at h
  change (cut (clock z) (rest z)).length + (skip (clock z) (rest z)).length = (rest z).length at h
  simp only [step, sel]
  split
  · omega
  · split
    · omega
    · simp only [pack, pairB_length, List.length_append, List.length_nil, clock, rest, output] at *
      omega

def split (q : Word × Word) : Word :=
  output (step^[q.2.length] (pack q.1 q.2 []))

theorem split_cpt : ComputableInPolyTime encodePair (fun x : Word => x) split := by
  obtain ⟨m⟩ := step_cpt
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 q.2 []) :=
    cptl (cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const []))))
      (fun q => by simp [pack, unpairB_pairB])
  have ht := Iter.iter_polyTime step m 3 step_bound
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pairG hs cpt_snd) ht) ho) (fun _ => rfl)

theorem step_enc (c row tail : Word) (out : List Word) (hc : c ≠ []) (hr : row.length = c.length) :
    step (pack c (row ++ tail) (wire out)) = pack c tail (wire (out ++ [row])) := by
  have hn : row ++ tail ≠ [] := by
    intro h
    simp only [List.append_eq_nil_iff] at h
    have he : row.length = 0 := by simp [h.1]
    rw [hr, List.length_eq_zero_iff] at he
    exact hc he
  have ht : (row ++ tail).take c.length = row := by rw [← hr, List.take_left]
  have hd : (row ++ tail).drop c.length = tail := by rw [← hr, List.drop_left]
  simp [step, pack, clock, rest, output, unpairB_pairB, sel, hc, hn,
    cut_eq, skip, ht, hd, wire_append, wire]

theorem scan (c : Word) (rows out : List Word) (hc : c ≠ [])
    (hr : ∀ r ∈ rows, r.length = c.length) :
    step^[rows.length] (pack c rows.flatten (wire out)) = pack c [] (wire (out ++ rows)) := by
  induction rows generalizing out with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatten_cons,
      step_enc c r rs.flatten out hc (hr r (by simp)), ih _ (fun a ha => hr a (by simp [ha]))]
    simp [List.append_assoc]

theorem halt (c out : Word) : step (pack c [] out) = pack c [] out := by
  simp [step, pack, clock, rest, unpairB_pairB, sel]

theorem count_rows (c : Word) (rows : List Word) (hc : c ≠ [])
    (hr : ∀ r ∈ rows, r.length = c.length) : rows.length ≤ rows.flatten.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    have hp := List.length_pos_iff.mpr hc
    have he := hr r (by simp)
    have hh := ih (fun a ha => hr a (by simp [ha]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem split_enc (c : Word) (rows : List Word) (hc : c ≠ [])
    (hr : ∀ r ∈ rows, r.length = c.length) : split (c, rows.flatten) = wire rows := by
  have hl := count_rows c rows hc hr
  unfold split
  change output (step^[rows.flatten.length] (pack c rows.flatten (wire []))) = _
  rw [← Nat.sub_add_cancel hl, Function.iterate_add_apply, scan c rows [] hc hr,
    Function.iterate_fixed (halt _ _)]
  simp [pack, output, unpairB_pairB]

end PEqualNP.Outside.RecordBlockSplit
