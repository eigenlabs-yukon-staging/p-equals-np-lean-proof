import PEqualNP.Outside.TripleObstructionMachine
import PEqualNP.Outside.CnfRestrictionMachine

namespace PEqualNP.Outside.BackdoorPathMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.TripleObstructionMachine (obstruction obstruction_cpt)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def formula (z : Word) : Word := (unpairB z).1
def selected (z : Word) : Word := (unpairB (unpairB z).2).1
def setTrue (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def code (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2

def pack (x s t b : Word) : Word := pairB x (pairB s (pairB t b))

/-- The reference bit-string toolbox's length-bounded copy of a word. -/
def cut (pad w : Word) : Word := (unpairB (mulU pad [true] ++ false :: w)).1

theorem cut_eq (pad w : Word) : cut pad w = w.take pad.length := by
  have h1 : (mulU pad [true] ++ false :: w).takeWhile id = un pad.length := by
    simp [mulU, un]
  have h2 : (mulU pad [true] ++ false :: w).dropWhile id = false :: w := by
    simp [mulU, un]
  simp [cut, unpairB, h1, h2, un]

theorem cut_cpt {p v : Word → Word} (hp : CPT p) (hv : CPT v) : CPT (fun z => cut (p z) (v z)) :=
  cpt_unpairB1_1 (cpt_app2 (cpt_mulU2 hp (cpt_const [true])) (cpt_cons1 false hv))

def pick (q b : Word) : Word :=
  sel (bflag (b.headD false)) (unpairB q).1
    (sel (bflag (b.tail.headD false)) (unpairB (unpairB q).2).1 (unpairB (unpairB q).2).2)

def step (z : Word) : Word :=
  let x := formula z
  let s := selected z
  let t := setTrue z
  let b := code z
  let q := obstruction (x, s)
  let v := cut x (pick q b)
  let add := sel (bflag (b.tail.tail.headD false)) [] v
  sel q z (pack x (s ++ v) (t ++ add) b.tail.tail.tail)

theorem step_cpt : CPT step := by
  have hx : CPT formula := cpt_unpairB1
  have hs : CPT selected := cpt_unpairB1_1 cpt_unpairB2
  have q₃ := cpt_unpairB2_1 cpt_unpairB2
  have ht : CPT setTrue := cpt_unpairB1_1 q₃
  have hb : CPT code := cpt_unpairB2_1 q₃
  have hq := cpt_comp (cpt_pair hx hs) obstruction_cpt
  have hq₂ := cpt_unpairB2_1 hq
  have hb₂ := cpt_tail1 hb
  have hb₃ := cpt_tail1 hb₂
  have hchoose := cpt_sel (cpt_comp hb cpt_firstF) (cpt_unpairB1_1 hq)
    (cpt_sel (cpt_comp hb₂ cpt_firstF) (cpt_unpairB1_1 hq₂) (cpt_unpairB2_1 hq₂))
  have hv := cut_cpt hx hchoose
  have htrue := cpt_sel (cpt_comp hb₃ cpt_firstF) (cpt_const []) hv
  have hnew := cpt_pairB2 hx (cpt_pairB2 (cpt_app2 hs hv)
    (cpt_pairB2 (cpt_app2 ht htrue) (cpt_tail1 hb₃)))
  exact cptl (cpt_sel hq cpt_id hnew) (fun _ => rfl)

def measure (z : Word) : ℕ := 4 * (formula z).length + 3

theorem formula_step (z : Word) : formula (step z) = formula z := by
  simp only [step, sel]
  split
  · rfl
  · simp [formula, pack, unpairB_pairB]

theorem step_growth (z : Word) : (step z).length ≤ z.length + measure z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  let v := cut (formula z) (pick (obstruction (formula z, selected z)) (code z))
  have hv : v.length ≤ (formula z).length := by
    simp [v, cut_eq, List.length_take]
  have htrue : (sel (bflag ((code z).tail.tail.headD false)) [] v).length ≤ v.length := by
    unfold sel
    split <;> simp
  change (sel (obstruction (formula z, selected z)) z
      (pack (formula z) (selected z ++ v)
        (setTrue z ++ sel (bflag ((code z).tail.tail.headD false)) [] v)
        (code z).tail.tail.tail)).length ≤ z.length + measure z
  unfold sel at htrue ⊢
  split
  · omega
  · simp only [pack, pairB_length, List.length_append, List.length_tail, measure,
      formula, selected, setTrue, code] at hv htrue ⊢
    omega

def endState (q : Word × Word) : Word :=
  step^[q.2.length] (pack q.1 [] [] q.2)

theorem endState_cpt : ComputableInPolyTime encodePair (fun x : Word => x) endState := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime_measure step m measure 4
    (fun z => by simp [measure, formula_step]) step_growth
    (fun z => by have h := unpairB_length z; simp only [measure, formula]; omega)
  have seed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) cpt_unpairB2)))
  have hseed : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 [] [] q.2) :=
    cptl seed (fun q => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_pairG hseed cpt_snd) loop
  exact h

def finish (z : Word) : Word :=
  CnfRestrictionMachine.run (formula z, pairB (selected z) (setTrue z))

def query (q : Word × Word) : Word := finish (endState q)

theorem query_cpt : ComputableInPolyTime encodePair (fun x : Word => x) query := by
  have h := cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB2) (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2))
  have hfinish := cpt_comp (cpt_pair cpt_unpairB1 h) CnfRestrictionMachine.run_cpt
  have hquery := cpt_comp endState_cpt hfinish
  exact hquery

end PEqualNP.Outside.BackdoorPathMachine
