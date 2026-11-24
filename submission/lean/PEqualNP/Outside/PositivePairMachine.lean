import PEqualNP.Outside.CnfRestrictionMachine
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.PositivePairMachine

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def known (z : Word) : Word := (unpairB z).1
def rest (z : Word) : Word := (unpairB (unpairB z).2).1
def first (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def found (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2

def pack (k r a f : Word) : Word := pairB k (pairB r (pairB a f))

def step (z : Word) : Word :=
  let k := known z
  let r := rest z
  let a := first z
  let v := (headI r).tail.tail
  let tail := dropI r
  let skip := pack k tail a []
  let close := pack k tail [] []
  let find := pack k tail [] (pairB a v)
  let add := sel a (pack k tail v []) find
  let active := sel r z
    (sel (bflag (isEnd r)) (sel (bflag (polB r)) skip (sel (bflag (memB v k)) add skip)) close)
  sel (found z) active z

theorem pack_cpt {k r a f : Word → Word}
    (hk : CPT k) (hr : CPT r) (ha : CPT a) (hf : CPT f) : CPT (fun z => pack (k z) (r z) (a z) (f z)) :=
  cpt_pairB2 hk (cpt_pairB2 hr (cpt_pairB2 ha hf))

theorem step_cpt : CPT step := by
  have hk : CPT known := cpt_unpairB1
  have q₂ := cpt_unpairB2
  have hr : CPT rest := cpt_unpairB1_1 q₂
  have q₃ := cpt_unpairB2_1 q₂
  have ha : CPT first := cpt_unpairB1_1 q₃
  have hf : CPT found := cpt_unpairB2_1 q₃
  have hv := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have ht := cpt_comp hr cpt_dropI
  have hn := cpt_const []
  have hskip := pack_cpt hk ht ha hn
  have hclose := pack_cpt hk ht hn hn
  have hfind := pack_cpt hk ht hn (cpt_pairB2 ha hv)
  have hadd := cpt_sel ha (pack_cpt hk ht hv hn) hfind
  have hpos := cpt_comp hr PEqualNP.Library.SearchHelpers.TwoSat.cpt_polF
  have hactive := cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF)
    (cpt_sel hpos hskip (cpt_sel (cpt_memB hv hk) hadd hskip)) hclose)
  exact cptl (cpt_sel hf hactive cpt_id) (fun _ => rfl)

theorem pack_length (k r a f : Word) :
    (pack k r a f).length = 2 * k.length + 2 * r.length + 2 * a.length + f.length + 3 := by
  simp only [pack, pairB_length]
  omega

theorem state_bound (z : Word) :
    2 * (known z).length + 2 * (rest z).length + 2 * (first z).length + (found z).length ≤ z.length := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  simp only [known, rest, first, found]
  omega

theorem step_length (z : Word) : (step z).length ≤ z.length + 5 := by
  have h := state_bound z
  have ht := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · split
    · omega
    · split
      · split
        · simp only [pack_length, List.length_nil]
          omega
        · split
          · split
            · simp only [pack_length, List.length_tail, List.length_nil]
              omega
            · simp only [pack_length, pairB_length, List.length_tail, List.length_nil]
              omega
          · simp only [pack_length, List.length_nil]
            omega
      · simp only [pack_length, List.length_nil]
        omega
  · omega

def obstruction (p : Word × Word) : Word :=
  found (step^[p.1.length] (pack p.2 p.1 [] []))

theorem obstruction_cpt : ComputableInPolyTime encodePair (fun x : Word => x) obstruction := by
  obtain ⟨c⟩ := step_cpt
  have loop := Iter.iter_polyTime step c 5 step_length
  have packed := cpt_comp cpt_pairB
    (pack_cpt cpt_unpairB2 cpt_unpairB1 (cpt_const []) (cpt_const []))
  have seed : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.2 q.1 [] []) :=
    cptl packed (fun q => by simp [unpairB_pairB])
  have hout : CPT found := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have h := cpt_comp (cpt_comp (cpt_pairG seed cpt_fst) loop) hout
  exact h

end PEqualNP.Outside.PositivePairMachine
