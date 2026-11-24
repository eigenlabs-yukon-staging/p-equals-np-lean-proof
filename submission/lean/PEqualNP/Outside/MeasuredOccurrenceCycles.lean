import PEqualNP.Outside.MeasuredOccurrenceSelection

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.CNFWidth (encodeCNF_append_local)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def arcWord (a b : Word) : Word := literalBits false a ++ literalBits true b ++ [false,false]

theorem arcWord_len (a b : Word) : (arcWord a b).length = 2*a.length+2*b.length+10 := by
  simp only [arcWord,List.length_append,List.length_cons,List.length_nil,literalBits_len]
  omega

theorem arcWord_enc (a b : ℕ) : arcWord a.bits b.bits = encodeClause (arc a b) := by
  simp [arcWord,literalBits_enc,encodeClause,arc,List.append_assoc]

theorem arcWord_cpt {a b : Word → Word} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => arcWord (a s) (b s)) :=
  cptl (cpt_app2 (cpt_app2 (cpt_comp ha (literalBits_cpt false))
    (cpt_comp hb (literalBits_cpt true))) (cpt_const [false,false])) (fun _ => rfl)

def cyPack (f c r o : Word) : Word := pairB f (pairB c (pairB r o))
def first (s : Word) := (unpairB s).1
def current (s : Word) := (unpairB (unpairB s).2).1
def remaining (s : Word) := (unpairB (unpairB (unpairB s).2).2).1
def cyclesOut (s : Word) := (unpairB (unpairB (unpairB s).2).2).2

def cycleStep (s : Word) : Word :=
  let r := remaining s
  let nxt := unpairB r
  sel r s (cyPack (first s) nxt.1 nxt.2 (cyclesOut s ++ arcWord (current s) nxt.1))

theorem cycleStep_cpt : CPT cycleStep := by
  have hF : CPT first := cpt_unpairB1
  have h2 := cpt_unpairB2
  have hC : CPT current := cpt_unpairB1_1 h2
  have h3 := cpt_unpairB2_1 h2
  have hR : CPT remaining := cpt_unpairB1_1 h3
  have hO : CPT cyclesOut := cpt_unpairB2_1 h3
  exact cptl (cpt_sel hR cpt_id (cpt_pairB2 hF (cpt_pairB2 (cpt_unpairB1_1 hR)
    (cpt_pairB2 (cpt_unpairB2_1 hR) (cpt_app2 hO (arcWord_cpt hC (cpt_unpairB1_1 hR)))))))
    (fun _ => rfl)

def cycleMeasure (s : Word) := 8*((first s).length+(current s).length+(remaining s).length)+16

theorem cycleState_bound (s : Word) :
    2*(first s).length+2*(current s).length+2*(remaining s).length+(cyclesOut s).length ≤ s.length := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  dsimp [first,current,remaining,cyclesOut]
  omega

theorem cycleMeasure_step (s : Word) : cycleMeasure (cycleStep s) ≤ cycleMeasure s := by
  by_cases h : remaining s = []
  · simp [cycleStep,sel,h]
  · have hb := unpairB_length (remaining s)
    rw [cycleStep,sel,ite_eq_right h]
    simp only [cycleMeasure,cyPack,first,current,remaining,unpairB_pairB] at *
    omega

theorem cycleStep_growth (s : Word) : (cycleStep s).length ≤ s.length + cycleMeasure s := by
  by_cases h : remaining s = []
  · simp [cycleStep,sel,h]
  · have hb := unpairB_length (remaining s)
    have hs := cycleState_bound s
    rw [cycleStep,sel,ite_eq_right h]
    simp only [cyPack,pairB_length,arcWord_len,List.length_append,cycleMeasure]
    omega

def closeCycle (s : Word) : Word := cyclesOut s ++ arcWord (current s) (first s)

theorem closeCycle_cpt : CPT closeCycle :=
  cpt_app2 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
    (arcWord_cpt (cpt_unpairB1_1 cpt_unpairB2) cpt_unpairB1)

def cycleRun (s : Word) : Word :=
  let h := unpairB s
  sel s [] (closeCycle (cycleStep^[s.length] (cyPack h.1 h.1 h.2 [])))

theorem cycleRun_cpt : CPT cycleRun := by
  obtain ⟨m⟩ := cycleStep_cpt
  have hi := Iter.iter_polyTime_measure cycleStep m cycleMeasure 16
    cycleMeasure_step cycleStep_growth (fun s => by have h := cycleState_bound s; unfold cycleMeasure; omega)
  have hp : CPT (fun s => cyPack (unpairB s).1 (unpairB s).1 (unpairB s).2 []) :=
    cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  exact cptl (cpt_sel cpt_id (cpt_const []) (cpt_comp (cpt_comp (cpt_pair hp cpt_id) hi) closeCycle_cpt))
    (fun _ => rfl)

theorem cycleStep_enc (f c n : ℕ) (ns : List ℕ) (o : Word) :
    cycleStep (cyPack f.bits c.bits (wire ((n::ns).map Nat.bits)) o) =
      cyPack f.bits n.bits (wire (ns.map Nat.bits)) (o ++ encodeClause (arc c n)) := by
  have hn : pairB n.bits (wire (ns.map Nat.bits)) ≠ [] := by simp [pairB]
  simp only [cycleStep,cyPack,first,current,remaining,cyclesOut,List.map_cons,wire,
    unpairB_pairB,sel,ite_eq_right hn,arcWord_enc]

theorem cycleStep_halt (f c o : Word) : cycleStep (cyPack f c [] o) = cyPack f c [] o := by
  simp [cycleStep,remaining,cyPack,unpairB_pairB,sel]

theorem cycleScan (f c : ℕ) (ns : List ℕ) (o : Word) :
    let z := cycleStep^[ns.length] (cyPack f.bits c.bits (wire (ns.map Nat.bits)) o)
    cycleStep z = z ∧ closeCycle z = o ++ encodeCNF (chain f c ns) := by
  induction ns generalizing c o with
  | nil =>
    refine ⟨cycleStep_halt ..,?_⟩
    simp [wire,closeCycle,cyPack,current,first,cyclesOut,unpairB_pairB,chain,encodeCNF,arcWord_enc]
  | cons n ns ih =>
    simp only [List.length_cons,Function.iterate_succ_apply,cycleStep_enc]
    simpa [chain,encodeCNF,List.append_assoc] using ih n (o++encodeClause (arc c n))

theorem cycleRun_enc (ns : List ℕ) :
    cycleRun (wire (ns.map Nat.bits)) = encodeCNF (cycle ns) := by
  cases ns with
  | nil => rfl
  | cons n ns =>
    have hb := wire_len ((n::ns).map Nat.bits)
    have hk : ns.length ≤ (wire ((n::ns).map Nat.bits)).length := by
      simp only [List.length_map,List.length_cons] at hb
      omega
    have hn : pairB n.bits (wire (ns.map Nat.bits)) ≠ [] := by simp [pairB]
    unfold cycleRun cycle
    simp only [List.map_cons,wire,unpairB_pairB,sel,ite_eq_right hn]
    have h := cycleScan n n ns []
    dsimp only at h
    rw [show (pairB n.bits (wire (ns.map Nat.bits))).length = _+ns.length from
      (Nat.sub_add_cancel hk).symm,Function.iterate_add_apply,Function.iterate_fixed h.1]
    simpa only [List.nil_append] using h.2

end PEqualNP.Outside.OccurrenceSplit
