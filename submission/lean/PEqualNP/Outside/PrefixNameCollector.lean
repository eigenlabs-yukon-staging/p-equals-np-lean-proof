import PEqualNP.Outside.CnfRestrictionMachine

namespace PEqualNP.Outside.PrefixNameCollector

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def rest (z : Word) : Word := (unpairB z).1
def older (z : Word) : Word := (unpairB (unpairB z).2).1
def newer (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def buf (z : Word) : Word := (unpairB (unpairB (unpairB (unpairB z).2).2).2).1
def out (z : Word) : Word := (unpairB (unpairB (unpairB (unpairB z).2).2).2).2
def pack (r o n b acc : Word) : Word := pairB r (pairB o (pairB n (pairB b acc)))

def step (z : Word) : Word :=
  let r := rest z
  let suffix := dropI r
  let l := pack suffix (newer z) (headI r).tail.tail (buf z ++ older z) (out z)
  let c := pack suffix [] [] [] (out z ++ buf z)
  sel r z (sel (bflag (isEnd r)) l c)

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have ho : CPT older := cpt_unpairB1_1 cpt_unpairB2
  have u₃ := cpt_unpairB2_1 cpt_unpairB2
  have hn : CPT newer := cpt_unpairB1_1 u₃
  have u₄ := cpt_unpairB2_1 u₃
  have hb : CPT buf := cpt_unpairB1_1 u₄
  have ha : CPT out := cpt_unpairB2_1 u₄
  have ht := cpt_comp hr cpt_dropI
  have hv := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have hl := cpt_pairB2 ht (cpt_pairB2 hn (cpt_pairB2 hv (cpt_pairB2 (cpt_app2 hb ho) ha)))
  have hc := cpt_pairB2 ht
    (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_app2 ha hb))))
  exact cptl (cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF) hl hc)) (fun _ => rfl)

theorem pack_length (r o n b acc : Word) :
    (pack r o n b acc).length =
      2 * r.length + 2 * o.length + 2 * n.length + 2 * b.length + acc.length + 4 := by
  simp only [pack, pairB_length]
  omega

theorem state_bound (z : Word) :
    2 * (rest z).length + 2 * (older z).length + 2 * (newer z).length +
      2 * (buf z).length + (out z).length ≤ z.length := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  have h₄ := unpairB_length (unpairB (unpairB (unpairB z).2).2).2
  simp only [rest, older, newer, buf, out]
  omega

theorem step_length (z : Word) : (step z).length ≤ z.length + 4 := by
  have h := state_bound z
  have ht := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at ht
  simp only [step, sel]
  split
  · omega
  · split
    · simp only [pack_length, List.length_append, List.length_tail]
      omega
    · simp only [pack_length, List.length_nil, List.length_append]
      omega

def collect (x : Word) : Word :=
  out (step^[x.length] (pack x [] [] [] []))

theorem collect_cpt : CPT collect := by
  obtain ⟨c⟩ := step_cpt
  have hLoop := Iter.iter_polyTime step c 4 step_length
  have hs := cpt_pairB2 cpt_id (cpt_const (pairB [] (pairB [] (pairB [] []))))
  have h := cpt_comp (cpt_comp (cpt_pair hs cpt_id) hLoop)
    (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)))
  exact h

end PEqualNP.Outside.PrefixNameCollector
