import PEqualNP.Outside.MeasuredOccurrenceCycles
import PEqualNP.Outside.OccurrenceModelEquiv
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.Tab.StepW (cpt_flatMapRange)
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.CNFWidth (encodeCNF_append_local)
open PEqualNP.Library.SearchHelpers.SatV (vcode vcode_injective)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def dropRec (s : Word) := (unpairB s).2

theorem dropRec_len (s : Word) : (dropRec s).length ≤ s.length + 0 := by
  have h := unpairB_length s
  unfold dropRec
  omega

def suffix (s : Word) : Word := dropRec^[(unpairB s).1.length] (unpairB s).2

theorem suffix_cpt : CPT suffix := by
  obtain ⟨m⟩ := (cpt_unpairB2 : CPT dropRec)
  exact cptl (cpt_comp (cpt_pair cpt_unpairB2 cpt_unpairB1)
    (Iter.iter_polyTime dropRec m 0 dropRec_len)) (fun _ => rfl)

theorem dropRec_enc (l : List Word) (i : ℕ) : dropRec^[i] (wire l) = wire (l.drop i) := by
  induction i generalizing l with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simpa [dropRec,wire,unpairB] using ih []
    | cons x xs =>
      rw [show dropRec (wire (x::xs)) = wire xs by simp [dropRec,wire,unpairB_pairB],ih]
      rfl

def lastCycle (q : Word × Word) : Word :=
  let k := (unpairB (unpairB q.2).1).1
  sel q.2 [] (sel (selectLabels (k,(unpairB q.2).2))
    (cycleRun (selectLabels (k,q.1))) [])

theorem lastCycle_cpt : ComputableInPolyTime encodePair (fun w : Word => w) lastCycle := by
  have hkey : CPT (fun s => (unpairB (unpairB (unpairB s).2).1).1) :=
    cpt_unpairB1_1 (cpt_unpairB1_1 cpt_unpairB2)
  have hwhole := cpt_comp (cpt_pair hkey cpt_unpairB1) selectLabels_cpt
  have htail := cpt_comp (cpt_pair hkey (cpt_unpairB2_1 cpt_unpairB2)) selectLabels_cpt
  have h := cpt_sel cpt_unpairB2 (cpt_const [])
    (cpt_sel htail (cpt_comp hwhole cycleRun_cpt) (cpt_const []))
  exact cptl (cpt_comp cpt_pairB h) (fun q => by simp [lastCycle,unpairB_pairB])

def suffixCycle (s : Word) : Word := lastCycle ((unpairB s).2,suffix s)

theorem suffixCycle_cpt : CPT suffixCycle :=
  cptl (cpt_comp (cpt_pair cpt_unpairB2 suffix_cpt) lastCycle_cpt) (fun _ => rfl)

def encodedLinks (s : Word) : Word :=
  (List.range s.length).flatMap fun i => suffixCycle (pairB (un i) s)

theorem encodedLinks_cpt : CPT encodedLinks :=
  cpt_flatMapRange suffixCycle_cpt cpt_id cpt_id


def recWord (r : ℕ × ℕ) : Word := pairB (vcode r.1) r.2.bits
def litPairs (j : ℕ) : Clause → List (ℕ × ℕ)
  | [] => []
  | l :: ls => (l.1,j) :: litPairs (j+1) ls

theorem items_eq (j : ℕ) (ls : Clause) : items j ls = (litPairs j ls).map recWord := by
  induction ls generalizing j with
  | nil => rfl
  | cons l ls ih => simp [items,litPairs,recWord,ih]

theorem pairs_fst (j : ℕ) (ls : Clause) : (litPairs j ls).map Prod.fst = ls.map Prod.fst := by
  induction ls generalizing j with
  | nil => rfl
  | cons l ls ih => simp [litPairs,ih]

theorem pairs_length (j : ℕ) (ls : Clause) : (litPairs j ls).length = ls.length := by
  simpa only [List.length_map] using congrArg List.length (pairs_fst j ls)

def labels (v : ℕ) (xs : List (ℕ × ℕ)) : List ℕ :=
  (xs.filter (fun r => r.1 == v)).map Prod.snd

theorem labels_nil (v : ℕ) (xs : List (ℕ × ℕ)) :
    labels v xs = [] ↔ v ∉ xs.map Prod.fst := by
  induction xs with
  | nil => simp [labels]
  | cons r rs ih =>
    by_cases hv : r.1 = v
    · simp [labels,hv]
    · have e : labels v (r::rs) = labels v rs := by simp [labels,hv]
      rw [e,ih,List.map_cons,List.mem_cons]
      simp [Ne.symm hv]

theorem selected_pairs (v : ℕ) (xs : List (ℕ × ℕ)) :
    selected (vcode v) (xs.map recWord) = (labels v xs).map Nat.bits := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    have ev : vcode r.1 = vcode v ↔ r.1 = v := vcode_injective.eq_iff
    by_cases h : r.1 = v
    · simp only [selected,labels,List.map_cons,List.filter_cons,recWord,unpairB_pairB,
        beq_iff_eq,h,ev,ite_true]
      exact congrArg (List.cons r.2.bits) ih
    · simp only [selected,labels,List.map_cons,List.filter_cons,recWord,unpairB_pairB,
        beq_iff_eq,h,ev,ite_false]
      exact ih

theorem wire_nil (ls : List Word) : wire ls = [] ↔ ls = [] := by
  cases ls with
  | nil => simp [wire]
  | cons l ls => simp [wire,pairB]

theorem selectPairs_enc (v : ℕ) (xs : List (ℕ × ℕ)) :
    selectLabels (vcode v,wire (xs.map recWord)) = wire ((labels v xs).map Nat.bits) := by
  rw [selectLabels_enc,selected_pairs]

theorem lastCycle_enc (full later : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    lastCycle (wire (full.map recWord),wire ((x::later).map recWord)) =
      if x.1 ∈ later.map Prod.fst then [] else encodeCNF (cycle (labels x.1 full)) := by
  have hn : pairB (pairB (vcode x.1) x.2.bits) (wire (later.map recWord)) ≠ [] := by simp [pairB]
  simp only [lastCycle,List.map_cons,wire,unpairB_pairB,recWord,sel,ite_eq_right hn]
  rw [selectPairs_enc,selectPairs_enc,cycleRun_enc]
  have hiff : wire ((labels x.1 later).map Nat.bits) = [] ↔
      x.1 ∉ later.map Prod.fst := by
    rw [wire_nil,List.map_eq_nil_iff,labels_nil]
  by_cases h : x.1 ∈ later.map Prod.fst
  · have hn' : wire ((labels x.1 later).map Nat.bits) ≠ [] := fun he => (hiff.mp he) h
    simp [h,hn',hn]
  · have hz := hiff.mpr h
    simp [h,hz,hn]

theorem suffixCycle_enc (full : List (ℕ × ℕ)) (i : ℕ) :
    suffixCycle (pairB (un i) (wire (full.map recWord))) =
      lastCycle (wire (full.map recWord),wire ((full.drop i).map recWord)) := by
  simp [suffixCycle,suffix,unpairB_pairB,un_length,dropRec_enc,← List.map_drop]

theorem scanLast (full tail : List (ℕ × ℕ)) (k : ℕ) (hk : tail.length ≤ k) :
    (List.range k).flatMap (fun i =>
      lastCycle (wire (full.map recWord),wire ((tail.drop i).map recWord))) =
        encodeCNF ((tail.map Prod.fst).dedup.flatMap (fun v => cycle (labels v full))) := by
  induction k generalizing tail with
  | zero =>
    have hh : tail = [] := List.length_eq_zero_iff.mp (by omega)
    subst tail
    rfl
  | succ k ih =>
    cases tail with
    | nil =>
      simp [lastCycle,wire,sel,encodeCNF]
    | cons x xs =>
      rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
      simp only [Function.comp_def,List.drop_zero,List.drop_succ_cons]
      rw [lastCycle_enc,ih xs (by simp only [List.length_cons] at hk; omega),List.map_cons]
      by_cases h : x.1 ∈ xs.map Prod.fst
      · simp [h,List.dedup_cons_of_mem]
      · simp [h,List.dedup_cons_of_notMem,encodeCNF_append_local]

theorem encodedLinks_enc (full : List (ℕ × ℕ)) :
    encodedLinks (wire (full.map recWord)) =
      encodeCNF ((full.map Prod.fst).dedup.flatMap (fun v => cycle (labels v full))) := by
  unfold encodedLinks
  simp only [suffixCycle_enc]
  exact scanLast full full _ (by simpa using wire_len (full.map recWord))


theorem pairs_range (j : ℕ) (ls : Clause) :
    litPairs j ls = (List.range ls.length).map
      (fun i => (((ls[i]?).getD (0,false)).1,j+i)) := by
  induction ls generalizing j with
  | nil => rfl
  | cons l ls ih =>
    rw [litPairs,ih,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [List.getElem?_cons_zero,Option.getD_some,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_def,List.getElem?_cons_succ]
    congr 1
    omega

theorem labels_range (F : CNF) (v : ℕ) :
    labels v (litPairs 0 F.flatten) = group F v := by
  rw [pairs_range]
  simp [labels,group,oldAt,List.filter_map,List.map_map,Function.comp_def]

theorem number_links (F : CNF) :
    encodedLinks (wire (items 0 F.flatten)) = encodeCNF (links F) := by
  rw [items_eq,encodedLinks_enc,pairs_fst,← ids_flatten]
  simp only [links,labels_range]

def compile (s : Word) : Word := mainOut (numberRun s) ++ encodedLinks (records (numberRun s))

theorem compile_cpt : CPT compile := by
  have htail := cpt_unpairB2_1 (cpt_unpairB2_1 numberRun_cpt)
  have hm := cpt_unpairB1_1 htail
  have ho := cpt_unpairB2_1 htail
  exact cptl (cpt_app2 hm (cpt_comp ho encodedLinks_cpt)) (fun _ => rfl)

theorem compile_enc (F : CNF) : compile (encodeCNF F) = encodeCNF (split F) := by
  rw [compile,numberRun_enc]
  simp only [opsPack,mainOut,records,unpairB_pairB,number_links,split,encodeCNF_append_local]

end PEqualNP.Outside.OccurrenceSplit

open PEqualNP.Library PEqualNP.Search

theorem PEqualNP.Outside.MeasuredOccurrenceLinks :
    ∃ F : List Bool → List Bool,
      ComputableInPolyTime (fun s : List Bool => s) (fun s : List Bool => s) F ∧
      ∀ φ : CNF, IsKCNF 3 φ →
        ∃ ψ : CNF, F (encodeCNF φ) = encodeCNF ψ ∧ IsKCNF 3 ψ ∧
          (∀ i : ℕ, (ψ.flatMap (List.map Prod.fst)).count i ≤ 3) ∧
          Nonempty (
            {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
              CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                then a ⟨i,h⟩ else false) φ = true} ≃
            {b : {i : ℕ // i ∈ ψ.flatMap (List.map Prod.fst)} → Bool //
              CNF.eval (fun i => if h : i ∈ ψ.flatMap (List.map Prod.fst)
                then b ⟨i,h⟩ else false) ψ = true}) := by
  open PEqualNP.Outside.OccurrenceSplit in
  exact ⟨compile,compile_cpt,fun φ h => ⟨split φ,compile_enc φ,split_width φ h,
    split_count φ,⟨modelsEquiv φ⟩⟩⟩
