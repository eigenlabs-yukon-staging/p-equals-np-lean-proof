import PEqualNP.Outside.MeasuredTruthTableLookup

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

private theorem zerosCpt : CPT (fun w => List.replicate w.length false) := by
  have h : CPT (List.filterMap (fun _ : Bool => some false)) :=
    filterMap_polyTime _ _ _ (fun _ => some false) (fun _ => rfl)
  refine bf_cptl h (fun w => ?_)
  induction w with
  | nil => rfl
  | cons b w ih => simp [List.replicate_succ,ih]

private theorem powBits (n a : Nat) :
    (List.replicate n false).foldl (fun v b => 2*v+b.toNat) a = a*2^n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.foldl_cons]
    change (List.replicate n false).foldl (fun v b => 2*v+b.toNat) (2*a) = a*2^(n+1)
    rw [ih,pow_succ]
    ring

private def block (fuel table : Word) : Word :=
  clippedIndex (true :: List.replicate fuel.length false) table

private theorem block_cpt : ComputableInPolyTime encodePair (fun x => x)
    (fun p : Word × Word => block p.1 p.2) := by
  have h := cpt_comp (cpt_pair (cpt_cons1 true (cpt_comp cpt_unpairB1 zerosCpt)) cpt_unpairB2)
    clippedIndex_cpt
  exact cpt_fromRaw (f := fun p : Word × Word => block p.1 p.2) h

private theorem block_length (fuel table : Word) :
    (block fuel table).length = min table.length (2^fuel.length) := by
  unfold block
  rw [clippedIndex_length]
  change min table.length ((List.replicate fuel.length false).foldl (fun a b => 2*a+b.toNat) 1) = _
  rw [powBits, Nat.one_mul]

private theorem tailIter (i : Nat) (w : Word) : (fun x : Word => x.tail)^[i] w = w.drop i := by
  induction i generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,ih]
    cases w <;> simp

private def restrictState (size : Word) (phase : Bool) (rem out : Word) : Word :=
  pairB size (pairB (bflag phase) (pairB rem out))

private def restrictStep (desired : Bool) (s : Word) : Word :=
  let size := (unpairB s).1
  let body := (unpairB s).2
  let phase := (unpairB body).1
  let rem := (unpairB (unpairB body).2).1
  let out := (unpairB (unpairB body).2).2
  let piece := rem.take size.length
  let output := if (!phase.isEmpty) == desired then out ++ piece else out
  sel rem s (pairB size (pairB (sel phase [true] []) (pairB (rem.drop size.length) output)))

private theorem restrictStep_cpt (desired : Bool) : CPT (restrictStep desired) := by
  have hsize := cpt_unpairB1
  have hphase := cpt_unpairB1_1 cpt_unpairB2
  have hp := cpt_unpairB2_1 cpt_unpairB2
  have hrem := cpt_unpairB1_1 hp
  have hout := cpt_unpairB2_1 hp
  have hflip := cpt_sel hphase (cpt_const [true]) (cpt_const [])
  have hdrop := cpt_iterLen cpt_tail (fun w => by simp) hsize hrem
  have hpiece := PEqualNP.Library.SearchHelpers.Tab.StepW.cpt_tk hsize hrem
  have hkeep := cpt_app2 hout hpiece
  cases desired
  · have hraw := cpt_sel hrem cpt_id (cpt_pairB2 hsize
      (cpt_pairB2 hflip (cpt_pairB2 hdrop (cpt_sel hphase hkeep hout))))
    refine bf_cptl hraw (fun s => ?_)
    unfold restrictStep
    simp only [tailIter,PEqualNP.Library.SearchHelpers.Tab.StepW.tk_eq]
    cases (unpairB (unpairB s).2).1 <;> rfl
  · have hraw := cpt_sel hrem cpt_id (cpt_pairB2 hsize
      (cpt_pairB2 hflip (cpt_pairB2 hdrop (cpt_sel hphase hout hkeep))))
    refine bf_cptl hraw (fun s => ?_)
    unfold restrictStep
    simp only [tailIter,PEqualNP.Library.SearchHelpers.Tab.StepW.tk_eq]
    cases (unpairB (unpairB s).2).1 <;> rfl

private def restrictMeasure (s : Word) : Nat := (unpairB s).1.length + 5

private theorem restrictMeasure_step (desired : Bool) (s : Word) :
    restrictMeasure (restrictStep desired s) ≤ restrictMeasure s := by
  unfold restrictStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [restrictMeasure,unpairB_pairB]

private theorem restrictStep_size (desired : Bool) (s : Word) :
    (restrictStep desired s).length ≤ s.length + restrictMeasure s := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  have h₃ := unpairB_length (unpairB (unpairB s).2).2
  unfold restrictStep
  dsimp only
  unfold sel
  split
  · omega
  · simp only [restrictMeasure,pairB_length,List.length_drop]
    split <;> split <;>
      simp only [List.length_append,List.length_take,List.length_cons,List.length_nil] <;> omega

private def restrictBlocks (desired : Bool) (blockSize rounds : Nat) (phase : Bool) (rem : Word) : Word :=
  Nat.rec (fun _ : Bool × Word => [])
    (fun _ run p =>
      (if p.1 == desired then p.2.take blockSize else []) ++
        run (!p.1,p.2.drop blockSize)) rounds (phase,rem)

private theorem emptyBlocks (desired phase : Bool) (size n : Nat) :
    restrictBlocks desired size n phase [] = [] := by
  induction n generalizing phase with
  | zero => rfl
  | succ n ih =>
    have he := ih (!phase)
    simp [restrictBlocks] at he
    cases phase <;> cases desired <;> simpa [restrictBlocks] using he

private theorem blockIter (desired : Bool) (size : Word) (n : Nat) (phase : Bool) (rem out : Word) :
    (unpairB (unpairB (unpairB ((restrictStep desired)^[n]
      (restrictState size phase rem out))).2).2).2 =
      out ++ restrictBlocks desired size.length n phase rem := by
  induction n generalizing phase rem out with
  | zero => simp [restrictState,restrictBlocks,unpairB_pairB]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases empty : rem = []
    · subst rem
      have he : restrictStep desired (restrictState size phase [] out) =
          restrictState size phase [] out := by simp [restrictStep,restrictState,unpairB_pairB]
      rw [he,ih,emptyBlocks,emptyBlocks]
    · let piece := if phase == desired then rem.take size.length else []
      have he : restrictStep desired (restrictState size phase rem out) =
          restrictState size (!phase) (rem.drop size.length) (out ++ piece) := by
        cases phase <;> cases desired <;>
          simp [restrictStep,restrictState,unpairB_pairB,sel,bflag,empty,piece]
      rw [he,ih]
      simp [restrictBlocks,List.append_assoc,piece]

private theorem restrictBlocks_clip (desired : Bool) (size cap n : Nat) (phase : Bool) (rem : Word)
    (h : rem.length ≤ cap) :
    restrictBlocks desired (min cap size) n phase rem = restrictBlocks desired size n phase rem := by
  by_cases e : size ≤ cap
  · rw [min_eq_right e]
  · have h' : rem.length ≤ size := h.trans (Nat.le_of_not_ge e)
    rw [min_eq_left (Nat.le_of_not_ge e)]
    cases n with
    | zero => rfl
    | succ n =>
      change (if phase == desired then rem.take cap else []) ++
        restrictBlocks desired cap n (!phase) (rem.drop cap) =
        (if phase == desired then rem.take size else []) ++
          restrictBlocks desired size n (!phase) (rem.drop size)
      simp [List.take_of_length_le h,List.take_of_length_le h',
        List.drop_eq_nil_of_le h,List.drop_eq_nil_of_le h',emptyBlocks]

private def bitFilter (desired : Bool) (i : Nat) (p : Bool × Nat) : Option Bool :=
  if p.2.testBit i == desired then some p.1 else none

private theorem block_filter (desired : Bool) (i m : Nat) (xs : Word)
    (hl : xs.length ≤ 2^i) :
    (xs.zipIdx (m*2^i)).filterMap (bitFilter desired i) =
      if m.testBit 0 == desired then xs else [] := by
  have same (p : Bool × Nat) (hp : p ∈ xs.zipIdx (m*2^i)) :
      p.2.testBit i = m.testBit 0 := by
    have upper := List.snd_lt_of_mem_zipIdx hp
    have lower : m*2^i ≤ p.2 := by
      obtain ⟨lo,_⟩ := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp hp
      exact lo
    let j := p.2 - m*2^i
    have hj : j < 2^i := by dsimp [j]; omega
    have eq : p.2 = 2^i*m+j := by
      rw [Nat.mul_comm (2^i) m]
      dsimp [j]
      omega
    rw [eq,Nat.testBit_two_pow_mul_add m hj]
    simp
  have applySame : (xs.zipIdx (m*2^i)).filterMap (bitFilter desired i) =
      (xs.zipIdx (m*2^i)).filterMap
        (fun p => if m.testBit 0 == desired then some p.1 else none) := by
    apply List.filterMap_congr
    intro p hp
    simp [bitFilter,same p hp]
  rw [applySame]
  cases h : m.testBit 0 == desired <;> simp [h,List.zipIdx_map_fst]

private theorem toggle_bit (m : Nat) : (m+1).testBit 0 = !m.testBit 0 := by
  have h := Nat.testBit_two_pow_add_eq m 0
  simpa [Nat.add_comm] using h

private theorem block_filter_all (desired : Bool) (i n m : Nat) (xs : Word)
    (hlen : xs.length ≤ n) :
    restrictBlocks desired (2^i) n (m.testBit 0) xs =
      (xs.zipIdx (m*2^i)).filterMap (bitFilter desired i) := by
  induction n generalizing xs m with
  | zero =>
    have e : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    let size := 2^i
    let left := xs.take size
    let right := xs.drop size
    have hsize : 0 < size := Nat.two_pow_pos i
    have hr : right.length ≤ n := by simp [right]; omega
    have hl : left.length ≤ size := by simp [left]
    have hzip : xs.zipIdx (m*size) =
        left.zipIdx (m*size) ++ right.zipIdx (m*size + left.length) := by
      rw [← List.zipIdx_append]
      simp [left,right,List.take_append_drop]
    have ha : right.zipIdx (m*size + left.length) = right.zipIdx ((m+1)*size) := by
      by_cases h : size ≤ xs.length
      · have e : left.length = size := by simp [left,Nat.min_eq_left h]
        rw [e,Nat.succ_mul]
      · have e : right = [] := List.drop_eq_nil_of_le (by omega)
        rw [e]
        rfl
    change (if m.testBit 0 == desired then left else []) ++
      restrictBlocks desired size n (!(m.testBit 0)) right =
      (xs.zipIdx (m*size)).filterMap (bitFilter desired i)
    rw [hzip,List.filterMap_append,ha,block_filter desired i m left hl]
    rw [← toggle_bit,ih (m+1) right hr]

/-- Uniformly retain alternating blocks, starting with the false phase. With
a block of size two to a supplied unary exponent, this restricts one truth-table
coordinate. The result remains measured for arbitrary input table lengths. -/
theorem MeasuredTruthTableRestriction (desired : Bool) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ fuel table : Word, run (fuel,table) =
        table.zipIdx.filterMap
          (fun p => if p.2.testBit fuel.length == desired then some p.1 else none) := by
  obtain ⟨c⟩ := restrictStep_cpt desired
  have h := Iter.iter_polyTime_measure (restrictStep desired) c restrictMeasure 5
    (restrictMeasure_step desired) (restrictStep_size desired)
    (fun s => by have h := unpairB_length s; unfold restrictMeasure; omega)
  have hb := cpt_comp cpt_unpairB block_cpt
  have hinit := cpt_pairB2 hb
    (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have hrun := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1
    (cpt_comp (cpt_pair hinit cpt_unpairB2) h)))
  let run := fun p : Word × Word =>
    (unpairB (unpairB (unpairB ((restrictStep desired)^[p.2.length]
      (restrictState (block p.1 p.2) false p.2 []))).2).2).2
  refine ⟨run,cpt_fromRaw (f := run) hrun,fun fuel table => ?_⟩
  unfold run
  rw [blockIter]
  simp only [List.nil_append,block_length]
  rw [restrictBlocks_clip desired _ _ _ _ _ le_rfl]
  have e := block_filter_all desired fuel.length table.length 0 table le_rfl
  change restrictBlocks desired (2^fuel.length) table.length false table =
    (table.zipIdx 0).filterMap (bitFilter desired fuel.length)
  simpa only [Nat.zero_mul,Nat.testBit_zero,Nat.zero_mod,Nat.zero_ne_one,decide_false] using e

end PEqualNP.Outside
