import PEqualNP.Outside.CnfRestrictionMachine

namespace PEqualNP.Outside.FirstWideCollector

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def rest (z : Word) : Word := (unpairB z).1
def count (z : Word) : Word := (unpairB (unpairB z).2).1
def buf (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).1
def out (z : Word) : Word := (unpairB (unpairB (unpairB z).2).2).2
def pack (r n b o : Word) : Word := pairB r (pairB n (pairB b o))

def step (z : Word) : Word :=
  let r := rest z
  let n := count z
  let b := buf z
  let o := out z
  let suffix := dropI r
  let lit := pack suffix (true :: n) (b ++ (headI r).tail.tail) o
  let close := pack suffix [] [] (sel n.tail.tail [] b)
  sel o (sel r z (sel (bflag (isEnd r)) lit close)) z

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have hn : CPT count := cpt_unpairB1_1 cpt_unpairB2
  have h₃ := cpt_unpairB2_1 cpt_unpairB2
  have hb : CPT buf := cpt_unpairB1_1 h₃
  have ho : CPT out := cpt_unpairB2_1 h₃
  have ht := cpt_comp hr cpt_dropI
  have hName := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have hlit := cpt_pairB2 ht (cpt_pairB2 (cpt_cons1 true hn) (cpt_pairB2 (cpt_app2 hb hName) ho))
  have hc := cpt_sel (cpt_tail1 (cpt_tail1 hn)) (cpt_const []) hb
  have hclose := cpt_pairB2 ht (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) hc))
  exact cptl (cpt_sel ho (cpt_sel hr cpt_id (cpt_sel (cpt_comp hr cpt_isEndF) hlit hclose))
    cpt_id) (fun _ => rfl)

theorem pack_length (r n b o : Word) :
    (pack r n b o).length = 2 * r.length + 2 * n.length + 2 * b.length + o.length + 3 := by
  simp only [pack, pairB_length]
  omega

theorem state_bound (z : Word) :
    2 * (rest z).length + 2 * (count z).length + 2 * (buf z).length + (out z).length ≤ z.length := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := unpairB_length (unpairB (unpairB z).2).2
  simp only [rest, count, buf, out]
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
      · simp only [pack_length, List.length_cons, List.length_append, List.length_tail]
        omega
      · simp only [pack_length, List.length_nil]
        split
        · simp only [List.length_nil]
          omega
        · omega
  · omega

def gather (x : Word) : Word :=
  out (step^[x.length] (pack x [] [] []))

theorem gather_cpt : CPT gather := by
  obtain ⟨c⟩ := step_cpt
  have hLoop := Iter.iter_polyTime step c 5 step_length
  have hs := cpt_pairB2 cpt_id (cpt_const (pairB [] (pairB [] [])))
  have h := cpt_comp (cpt_comp (cpt_pair hs cpt_id) hLoop)
    (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  exact h

end PEqualNP.Outside.FirstWideCollector
