import PEqualNP.Outside.SparseImageCandidatePruning
import PEqualNP.Outside.AllRecordTest
import PEqualNP.Outside.RecordPrefixQueries
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside.SparseImagePruneMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.RecordPrefixQueries (wire_append)
open PEqualNP.Outside.AllRecordTest (check check_cpt check_enc)
open PEqualNP.Outside.SparseImageCandidatePruning (pruneCollision prune)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def records (as : List (Word × Word)) : Word := wire (as.map (fun a => pairB a.1 a.2))
def unequal (q : Word × Word) : Bool := decide ((unpairB q.1).2 ≠ q.2)

theorem unequal_cpt : ComputableInPolyTime encodePair Computability.encodeBool unequal := by
  have h1 := cpt_unpairB2_1 cpt_unpairB1
  have h2 := cpt_unpairB2
  have h := cpt_comp (PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF h1 h2) cpt_isEmpty
  exact cptl (cpt_comp cpt_pairB h) (fun q => by
    by_cases he : (unpairB q.1).2 = q.2 <;> simp [unequal, unpairB_pairB, bflag, he])

theorem check_records (as : List (Word × Word)) (r : Word) :
    check unequal (records as,r) = true ↔ r ∉ as.map Prod.snd := by
  rw [records, check_enc]
  constructor
  · intro h hm
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
    have hu := h (pairB a.1 a.2) (List.mem_map.mpr ⟨a,ha,rfl⟩)
    simp only [unequal, unpairB_pairB, decide_eq_true_eq] at hu
    exact hu he
  · intro h y hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
    simp only [unequal, unpairB_pairB, decide_eq_true_eq]
    exact fun he => h (List.mem_map.mpr ⟨a,ha,he⟩)

def pack (done r out : Word) : Word := pairB done (pairB r out)
def done (z : Word) : Word := (unpairB z).1
def rest (z : Word) : Word := (unpairB (unpairB z).2).1
def output (z : Word) : Word := (unpairB (unpairB z).2).2

def step (z : Word) : Word :=
  let d := done z
  let r := rest z
  let o := output z
  let a := unpairB r
  let p := unpairB a.1
  let fresh := bflag (check unequal (a.2, p.2))
  let keep := pack d a.2 (o ++ pairB p.1 [])
  sel r z (sel d (sel fresh (pack [true] a.2 o) keep) keep)

theorem step_cpt : CPT step := by
  have hd : CPT done := cpt_unpairB1
  have hr : CPT rest := cpt_unpairB1_1 cpt_unpairB2
  have ho : CPT output := cpt_unpairB2_1 cpt_unpairB2
  have ht := cpt_unpairB2_1 hr
  have hc := cpt_unpairB1_1 hr
  have hf := cpt_bitFlag (cpt_comp (cpt_pair ht (cpt_unpairB2_1 hc)) (check_cpt unequal unequal_cpt))
  have hkeep := cpt_pairB2 hd (cpt_pairB2 ht
    (cpt_app2 ho (cpt_pairB2 (cpt_unpairB1_1 hc) (cpt_const []))))
  have hdrop := cpt_pairB2 (cpt_const [true]) (cpt_pairB2 ht ho)
  exact cptl (cpt_sel hr cpt_id (cpt_sel hd (cpt_sel hf hdrop hkeep) hkeep))
    (fun _ => rfl)

theorem step_size (z : Word) : (step z).length ≤ z.length + 4 := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have h3 := unpairB_length (rest z)
  have h4 := unpairB_length (unpairB (rest z)).1
  simp only [step, sel]
  split
  · omega
  · split
    · split <;> simp only [pack,pairB_length,List.length_append,List.length_nil,List.length_cons,
        done,rest,output] at * <;> omega
    · simp only [pack,pairB_length,List.length_append,List.length_nil,done,rest,output] at *
      omega

def endState (r : Word) : Word := step^[r.length] (pack [] r [])
def execute (q : Word × Word) : Word :=
  let z := endState q.2
  sel (done z) (output z) (pairB q.1 (output z))

theorem endState_cpt : CPT endState := by
  obtain ⟨m⟩ := step_cpt
  have hs : CPT (fun r => pack [] r []) :=
    cptl (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_id (cpt_const []))) (fun _ => rfl)
  exact cptl (cpt_comp (cpt_pair hs cpt_id) (Iter.iter_polyTime step m 4 step_size))
    (fun _ => rfl)

theorem execute_cpt : ComputableInPolyTime encodePair (fun x : Word => x) execute := by
  have hz := cpt_comp cpt_unpairB2 endState_cpt
  have hd := cpt_unpairB1_1 hz
  have ho := cpt_unpairB2_1 (cpt_unpairB2_1 hz)
  exact cptl (cpt_comp cpt_pairB (cpt_sel hd ho (cpt_pairB2 cpt_unpairB1 ho)))
    (fun q => by simp [execute, done,output,unpairB_pairB])

theorem fixed (d o : Word) : step (pack d [] o) = pack d [] o := by
  simp [step, rest, pack, unpairB_pairB, sel]

theorem step_records (d : Word) (a : Word × Word) (as : List (Word × Word)) (acc : List Word) :
    step (pack d (records (a :: as)) (wire acc)) =
      if d = [] ∧ a.2 ∈ as.map Prod.snd then pack [true] (records as) (wire acc)
      else pack d (records as) (wire (acc ++ [a.1])) := by
  have hn : pairB (pairB a.1 a.2) (records as) ≠ [] := by simp [pairB]
  have hw : records (a :: as) = pairB (pairB a.1 a.2) (records as) := rfl
  have hf := check_records as a.2
  rw [hw]
  simp only [step, done,rest,output,pack,unpairB_pairB,sel,hn,if_false, wire_append, wire,
    List.append_nil]
  by_cases hd : d = []
  · by_cases hm : a.2 ∈ as.map Prod.snd
    · have hf' : check unequal (records as,a.2) = false := by
        cases h : check unequal (records as,a.2)
        · rfl
        · exact False.elim ((hf.mp h) hm)
      simp [hd,hm,hf',bflag]
    · simp [hd,hm,hf.mpr hm,bflag]
  · simp [hd]

theorem after_drop (as : List (Word × Word)) (acc : List Word) :
    step^[as.length] (pack [true] (records as) (wire acc)) =
      pack [true] [] (wire (acc ++ as.map Prod.fst)) := by
  induction as generalizing acc with
  | nil => simp [records,wire]
  | cons a as ih =>
    rw [List.length_cons, Function.iterate_succ_apply, step_records]
    simp [ih, List.append_assoc]

theorem scan (as : List (Word × Word)) (acc : List Word) :
    step^[as.length] (pack [] (records as) (wire acc)) =
      match pruneCollision as with
      | none => pack [] [] (wire (acc ++ as.map Prod.fst))
      | some bs => pack [true] [] (wire (acc ++ bs.map Prod.fst)) := by
  induction as generalizing acc with
  | nil => simp [records,wire,pruneCollision]
  | cons a as ih =>
    rw [List.length_cons, Function.iterate_succ_apply, step_records]
    by_cases hm : a.2 ∈ as.map Prod.snd
    · simp [hm, pruneCollision, after_drop]
    · simp only [hm, and_false, if_false, pruneCollision, ih]
      cases h : pruneCollision as <;> simp [h, List.append_assoc]

theorem execute_enc (pivot : Word) (as : List (Word × Word)) :
    execute (pivot, records as) = wire (prune pivot as) := by
  have hw : as.length ≤ (records as).length := by
    simpa only [records, List.length_map] using wire_len (as.map (fun a => pairB a.1 a.2))
  unfold execute endState
  simp only
  have hscan := scan as []
  simp only [wire, List.nil_append] at hscan
  rw [← Nat.sub_add_cancel hw, Function.iterate_add_apply, hscan]
  cases h : pruneCollision as with
  | none =>
    simp only [h]
    rw [Function.iterate_fixed (fixed _ _)]
    simp [h, done,output,pack,sel,unpairB_pairB,prune]
  | some bs =>
    simp only [h]
    rw [Function.iterate_fixed (fixed _ _)]
    simp [h, done,output,pack,sel,unpairB_pairB,prune,wire]

end PEqualNP.Outside.SparseImagePruneMachine

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.SparseImagePruneMachine (execute execute_cpt execute_enc records)
open PEqualNP.Outside.SparseImageCandidatePruning (prune prune_sublist prune_preserves)
open PEqualNP.Outside.RecordPairScan (wire)

theorem PEqualNP.Outside.SparseImagePruneMachine :
    ∃ (E : List (List Bool) → List Bool)
      (shrink : List Bool → List (List Bool × List Bool) → List (List Bool))
      (F : (List Bool × List Bool) → List Bool),
      E [] = [] ∧
      (∀ a as, E (a :: as) = List.replicate a.length true ++ false :: (a ++ E as)) ∧
      ComputableInPolyTime encodePair (fun w => w) F ∧
      ∀ (pivot : List Bool) (as : List (List Bool × List Bool)),
        F (pivot, E (as.map (fun a => List.replicate a.1.length true ++ false :: (a.1 ++ a.2)))) =
          E (shrink pivot as) ∧
        (shrink pivot as).Sublist (pivot :: as.map Prod.fst) ∧
        (shrink pivot as).length + 1 = as.length + 1 ∧
        ∀ (G : List Bool → Prop) (S : Finset (List Bool)),
          S.card < as.length → (∀ q ∈ as, q.2 ∈ S ↔ G pivot ∨ G q.1) →
          ((∃ x ∈ shrink pivot as, G x) ↔ G pivot ∨ ∃ q ∈ as, G q.1) := by
  refine ⟨wire, prune, execute, rfl, fun _ _ => rfl, execute_cpt, ?_⟩
  intro pivot as
  exact ⟨execute_enc pivot as, (prune_sublist pivot as).1, (prune_sublist pivot as).2,
    fun G S => prune_preserves G S pivot as⟩
