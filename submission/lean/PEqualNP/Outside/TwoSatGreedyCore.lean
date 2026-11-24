import PEqualNP.Outside.HornRenameMachine
import PEqualNP.Outside.BackdoorPathCore
import PEqualNP.Library.L030

namespace PEqualNP.Outside.TwoSatGreedyCore

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.FirstWideCollector (Word pack pack_length)
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Outside.BackdoorPathCore (cut cut_cpt cut_eq)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def problem (z : Word) : Word := (unpairB z).1
def cursor (z : Word) : Word := (unpairB (unpairB z).2).1
def chosen (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def trueNames (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2

def name (z : Word) : Word := cut (cursor z) (headI (cursor z)).tail.tail

theorem name_cpt : CPT name :=
  cut_cpt (cpt_unpairB1_1 cpt_unpairB2)
    (cpt_tail1 (cpt_tail1 (cpt_comp (cpt_unpairB1_1 cpt_unpairB2) cpt_headI)))

def trial (z : Word) : Word :=
  CnfRestrictionMachine.run (problem z, pairB (chosen z ++ name z) (trueNames z))

theorem trial_cpt : CPT trial := by
  have hb := cpt_unpairB2_1 cpt_unpairB2
  have ha := cpt_pairB2 (cpt_app2 (cpt_unpairB1_1 hb) name_cpt) (cpt_unpairB2_1 hb)
  have h := cpt_comp (cpt_pair cpt_unpairB1 ha) CnfRestrictionMachine.run_cpt
  exact h

def step (dec : Word → Bool) (z : Word) : Word :=
  let p := problem z
  let r := cursor z
  let s := chosen z
  let v := trueNames z
  let i := name z
  let tail := dropI r
  let advance := pack p tail s v
  let assign := pack p tail (s ++ i) (sel (bflag (dec (trial z))) (v ++ i) v)
  sel r z (sel (bflag (isEnd r)) (sel (bflag (memB i s)) assign advance) advance)

theorem step_cpt {dec : Word → Bool}
    (hdec : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool dec) :
    CPT (step dec) := by
  have hp : CPT problem := cpt_unpairB1
  have hr : CPT cursor := cpt_unpairB1_1 cpt_unpairB2
  have hb := cpt_unpairB2_1 cpt_unpairB2
  have hs : CPT chosen := cpt_unpairB1_1 hb
  have hv : CPT trueNames := cpt_unpairB2_1 hb
  have ht := cpt_comp hr cpt_dropI
  have hadv := cpt_pairB2 hp (cpt_pairB2 ht (cpt_pairB2 hs hv))
  have htest := cpt_bitFlag (cpt_comp trial_cpt hdec)
  have hnext := cpt_sel htest (cpt_app2 hv name_cpt) hv
  have hassign := cpt_pairB2 hp (cpt_pairB2 ht (cpt_pairB2 (cpt_app2 hs name_cpt) hnext))
  exact cptl (cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF)
    (cpt_sel (cpt_memB name_cpt hs) hassign hadv) hadv)) (fun _ => rfl)

def measure (z : Word) : ℕ := 3 * (cursor z).length + 3

theorem cursor_le (dec : Word → Bool) (z : Word) : (cursor (step dec z)).length ≤ (cursor z).length := by
  have hd := dropI_length (cursor z)
  simp only [step, sel]
  split
  · rfl
  · split
    · split
      · split <;> simpa [cursor, pack, unpairB_pairB] using hd
      · simpa [cursor, pack, unpairB_pairB] using hd
    · simpa [cursor, pack, unpairB_pairB] using hd

theorem step_length (dec : Word → Bool) (z : Word) : (step dec z).length ≤ z.length + measure z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  have hd := dropI_length (cursor z)
  have hn : (name z).length ≤ (cursor z).length := by simp [name, cut_eq, List.length_take]
  have hs : 2 * (problem z).length + 2 * (cursor z).length + 2 * (chosen z).length +
      (trueNames z).length ≤ z.length := by
    simp only [problem, cursor, chosen, trueNames]
    omega
  have ha : (pack (problem z) (dropI (cursor z)) (chosen z) (trueNames z)).length ≤
      z.length + measure z := by
    rw [pack_length]
    unfold measure
    omega
  simp only [step, sel]
  split
  · omega
  · split
    · split
      · split <;> simp only [pack_length, List.length_append, measure] <;> omega
      · exact ha
    · exact ha

def finish (dec : Word → Bool) (q : Word × Word) : Word :=
  trueNames ((step dec)^[q.1.length] (pack q.2 q.1 [] []))

theorem finish_cpt {dec : Word → Bool}
    (hdec : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool dec) :
    ComputableInPolyTime encodePair (fun x : Word => x) (finish dec) := by
  obtain ⟨m⟩ := step_cpt hdec
  have loop := Iter.iter_polyTime_measure (step dec) m measure 3
    (fun z => by have h := cursor_le dec z; unfold measure; omega) (step_length dec)
    (fun z => by
      have h₁ := unpairB_length z
      have h₂ := unpairB_length (unpairB z).2
      simp only [measure, cursor]
      omega)
  have hseed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const (pairB [] []))))
  have hs : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.2 q.1 [] []) :=
    cptl hseed (fun q => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_comp (cpt_pairG hs cpt_fst) loop)
    (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact h

end PEqualNP.Outside.TwoSatGreedyCore
