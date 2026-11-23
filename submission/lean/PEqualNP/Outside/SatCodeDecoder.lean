import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.SatCodeDecoder

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def remaining (z : Word) : Word := (unpairB z).1
def seen (z : Word) : Word := (unpairB (unpairB z).2).1
def bits (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def output (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2
def item (z : Word) : Word := (headI (remaining z)).tail.tail
def pack (r s b w : Word) : Word := pairB r (pairB s (pairB b w))

def step (z : Word) : Word :=
  let v := item z
  let old := pairB (seen z) (pairB (bits z) (output z))
  let new := pairB (seen z ++ v) (pairB (bits z).tail
    (output z ++ sel (bflag ((bits z).headD false)) [] v))
  pairB (dropI (remaining z)) (sel v old (sel (bflag (memB v (seen z))) new old))

def finalState (q : Word × Word) : Word :=
  step^[q.1.length] (pack q.1 [] q.2 [])

def decode (q : Word × Word) : Word :=
  output (finalState q)

theorem step_cpt : CPT step := by
  have hR : CPT remaining := cpt_unpairB1
  have hS : CPT seen := cpt_unpairB1_1 cpt_unpairB2
  have h3 := cpt_unpairB2_1 cpt_unpairB2
  have hB : CPT bits := cpt_unpairB1_1 h3
  have hO : CPT output := cpt_unpairB2_1 h3
  have hI : CPT item := cpt_tail1 (cpt_tail1 (cpt_comp hR cpt_headI))
  have hflag := cpt_memB hI hS
  have hm := cpt_sel (cpt_comp hB cpt_firstF) (cpt_const []) hI
  have old := cpt_pairB2 hS (cpt_pairB2 hB hO)
  have new := cpt_pairB2 (cpt_app2 hS hI) (cpt_pairB2 (cpt_tail1 hB) (cpt_app2 hO hm))
  exact cptl (cpt_pairB2 (cpt_comp hR cpt_dropI)
    (cpt_sel hI old (cpt_sel hflag new old))) (fun _ => rfl)

theorem item_length (z : Word) : (item z).length ≤ (remaining z).length := by
  have h := congrArg List.length (headI_dropI (remaining z))
  simp only [List.length_append] at h
  unfold item
  simp only [List.length_tail]
  omega

theorem step_growth (z : Word) :
    (step z).length ≤ z.length + (3 * (remaining z).length + 3) := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have h3 := unpairB_length (unpairB (unpairB z).2).2
  have h4 := dropI_length (remaining z)
  have h5 := item_length z
  have h6 : (sel (bflag ((bits z).headD false)) [] (item z)).length ≤ (item z).length := by
    unfold sel
    split <;> simp
  let old := pairB (seen z) (pairB (bits z) (output z))
  let new := pairB (seen z ++ item z) (pairB (bits z).tail
    (output z ++ sel (bflag ((bits z).headD false)) [] (item z)))
  let bound := 2 * (seen z).length + 2 * (bits z).length + (output z).length +
    3 * (item z).length + 2
  have ho : old.length ≤ bound := by
    simp only [old, bound, pairB_length]
    omega
  have hn : new.length ≤ bound := by
    simp only [new, bound, pairB_length, List.length_append, List.length_tail]
    omega
  have hs : (sel (item z) old (sel (bflag (memB (item z) (seen z))) new old)).length ≤ bound := by
    unfold sel
    split
    · exact ho
    · split <;> assumption
  change (pairB (dropI (remaining z))
    (sel (item z) old (sel (bflag (memB (item z) (seen z))) new old))).length ≤ _
  rw [pairB_length]
  simp only [bound, seen, bits, output] at hs
  simp only [remaining] at h4 h5
  simp only [remaining, seen] 
  omega

theorem measure_decreases (z : Word) :
    3 * (remaining (step z)).length + 3 ≤ 3 * (remaining z).length + 3 := by
  simp only [remaining, step, unpairB_pairB]
  have h := dropI_length (remaining z)
  unfold remaining at h
  omega

theorem finalState_cpt : ComputableInPolyTime encodePair (fun x : Word => x) finalState := by
  obtain ⟨c⟩ := step_cpt
  have hloop := Iter.iter_polyTime_measure step c (fun z => 3 * (remaining z).length + 3) 3
    measure_decreases step_growth (fun z => by have h := unpairB_length z; unfold remaining; omega)
  have hx : ComputableInPolyTime encodePair (fun x : Word => x) (fun q : Word × Word => q.1) :=
    cpt_fst
  have hseed : CPT (fun z => pack (unpairB z).1 [] (unpairB z).2 []) :=
    cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have hpack : ComputableInPolyTime encodePair (fun x : Word => x) (fun q => pack q.1 [] q.2 []) :=
    cptl (cpt_comp cpt_pairB hseed) (fun q => by simp [unpairB_pairB])
  exact cptl (cpt_comp (cpt_pairG hpack hx) hloop) (fun _ => rfl)

theorem decode_cpt : ComputableInPolyTime encodePair (fun x : Word => x) decode := by
  have h := cpt_comp finalState_cpt (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact h

theorem seen_cpt : ComputableInPolyTime encodePair (fun x : Word => x)
    (fun q => seen (finalState q)) := by
  have h := cpt_comp finalState_cpt (cpt_unpairB1_1 cpt_unpairB2)
  exact h

end PEqualNP.Outside.SatCodeDecoder
