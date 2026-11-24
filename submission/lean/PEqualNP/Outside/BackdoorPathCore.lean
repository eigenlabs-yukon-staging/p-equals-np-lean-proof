import PEqualNP.Outside.CnfRestrictionMachine

namespace PEqualNP.Outside.BackdoorPathCore

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives

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

def advanceUsing (probe choose : Word → Word) (z : Word) : Word :=
  let x := formula z
  let s := selected z
  let t := setTrue z
  let b := code z
  let q := probe z
  let v := cut x (choose z)
  let add := sel (bflag (b.tail.tail.headD false)) [] v
  sel q z (pack x (s ++ v) (t ++ add) b.tail.tail.tail)

theorem advanceUsing_cpt {probe choose : Word → Word} (hq : CPT probe) (hchoose : CPT choose) :
    CPT (advanceUsing probe choose) := by
  have hx : CPT formula := cpt_unpairB1
  have hs : CPT selected := cpt_unpairB1_1 cpt_unpairB2
  have q₃ := cpt_unpairB2_1 cpt_unpairB2
  have ht : CPT setTrue := cpt_unpairB1_1 q₃
  have hb : CPT code := cpt_unpairB2_1 q₃
  have hb₃ := cpt_tail1 (cpt_tail1 hb)
  have hv := cut_cpt hx hchoose
  have htrue := cpt_sel (cpt_comp hb₃ cpt_firstF) (cpt_const []) hv
  have hnew := cpt_pairB2 hx (cpt_pairB2 (cpt_app2 hs hv)
    (cpt_pairB2 (cpt_app2 ht htrue) (cpt_tail1 hb₃)))
  exact cptl (cpt_sel hq cpt_id hnew) (fun _ => rfl)

def measure (z : Word) : ℕ := 4 * (formula z).length + 3

theorem formula_advance (probe choose : Word → Word) (z : Word) :
    formula (advanceUsing probe choose z) = formula z := by
  simp only [advanceUsing, sel]
  split
  · rfl
  · simp [formula, pack, unpairB_pairB]

theorem advance_growth (probe choose : Word → Word) (z : Word) :
    (advanceUsing probe choose z).length ≤ z.length + measure z := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  let v := cut (formula z) (choose z)
  have hv : v.length ≤ (formula z).length := by
    simp [v, cut_eq, List.length_take]
  have htrue : (sel (bflag ((code z).tail.tail.headD false)) [] v).length ≤ v.length := by
    unfold sel
    split <;> simp
  change (sel (probe z) z
      (pack (formula z) (selected z ++ v)
        (setTrue z ++ sel (bflag ((code z).tail.tail.headD false)) [] v)
        (code z).tail.tail.tail)).length ≤ z.length + measure z
  unfold sel at htrue ⊢
  split
  · omega
  · simp only [pack, pairB_length, List.length_append, List.length_tail, measure,
      formula, selected, setTrue, code] at hv htrue ⊢
    omega

def endStateUsing (probe choose : Word → Word) (q : Word × Word) : Word :=
  (advanceUsing probe choose)^[q.2.length] (pack q.1 [] [] q.2)

theorem endStateUsing_cpt {probe choose : Word → Word} (hp : CPT probe) (hc : CPT choose) :
    ComputableInPolyTime encodePair (fun x : Word => x) (endStateUsing probe choose) := by
  obtain ⟨m⟩ := advanceUsing_cpt hp hc
  have loop := Iter.iter_polyTime_measure (advanceUsing probe choose) m measure 4
    (fun z => by simp [measure, formula_advance]) (advance_growth probe choose)
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

theorem finish_cpt : CPT finish := by
  have h := cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB2) (cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2))
  have hfinish := cpt_comp (cpt_pair cpt_unpairB1 h) CnfRestrictionMachine.run_cpt
  exact hfinish

end PEqualNP.Outside.BackdoorPathCore
