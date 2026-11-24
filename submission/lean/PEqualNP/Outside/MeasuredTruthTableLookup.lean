import PEqualNP.Outside.LexicographicWordCompare
import PEqualNP.Library.Machines.IterMeasure
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Outside.FrontierFilterByParameter

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

private def lookupState (cap bits index : Word) : Word := pairB cap (pairB bits index)

private def indexStep (s : Word) : Word :=
  let cap := (unpairB s).1
  let bits := (unpairB (unpairB s).2).1
  let index := (unpairB (unpairB s).2).2
  let next := index ++ index ++ bflag (bits.headD false)
  let clipped := sel (bflag (decide (next.length ≤ cap.length))) cap next
  sel bits s (lookupState cap bits.tail clipped)

private theorem indexStep_cpt : CPT indexStep := by
  have hc := cpt_unpairB1
  have hb := cpt_unpairB1_1 cpt_unpairB2
  have hi := cpt_unpairB2_1 cpt_unpairB2
  have hn := cpt_app2 (cpt_app2 hi hi) (cpt_bitFlag (cpt_comp hb wordHead_polyTime))
  have hh := cpt_bitFlag (cpt_comp (cpt_pair hc hn) LenCmp.lenLE_polyTime)
  have hr := cpt_sel hh hc hn
  exact cpt_sel hb cpt_id (cpt_pairB2 hc (cpt_pairB2 (cpt_tail1 hb) hr))

private def indexMeasure (s : Word) : Nat := (unpairB s).1.length + 2

private theorem indexMeasure_step (s : Word) : indexMeasure (indexStep s) ≤ indexMeasure s := by
  unfold indexStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [indexMeasure,lookupState,unpairB_pairB]

private theorem indexStep_size (s : Word) :
    (indexStep s).length ≤ s.length + indexMeasure s := by
  have hs := unpairB_length s
  have hinner := unpairB_length (unpairB s).2
  unfold indexStep
  dsimp only
  unfold sel
  split
  · omega
  · split
    · simp only [indexMeasure,lookupState,pairB_length,List.length_tail]
      omega
    · rename_i h
      have hcap := (not_congr (bflag_eq_nil _)).mp h
      simp only [Bool.not_eq_false,decide_eq_true_eq] at hcap
      simp only [indexMeasure,lookupState,pairB_length,List.length_tail]
      omega

private def binaryStep (a : Nat) (b : Bool) : Nat := 2*a+b.toNat

private theorem clip_step (cap a : Nat) (b : Bool) :
    min cap (binaryStep (min cap a) b) = min cap (binaryStep a b) := by
  by_cases h : a ≤ cap
  · rw [min_eq_right h]
  · have h₁ : cap ≤ a := by omega
    have h₂ : cap ≤ binaryStep cap b := by unfold binaryStep; omega
    have h₃ : cap ≤ binaryStep a b := by unfold binaryStep; omega
    rw [min_eq_left h₁,min_eq_left h₂,min_eq_left h₃]

private theorem indexStep_clip (cap index : Word) (b : Bool) (bits : Word) :
    ∃ i : Word, i.length = min cap.length (binaryStep index.length b) ∧
      indexStep (lookupState cap (b::bits) index) = lookupState cap bits i := by
  let next := index ++ index ++ bflag b
  have hlen : next.length = binaryStep index.length b := by
    cases b <;> simp [next,binaryStep,Bool.toNat,bflag,Nat.two_mul,Nat.add_assoc]
  have hstate : indexStep (lookupState cap (b::bits) index) =
      lookupState cap bits (sel (bflag (decide (next.length ≤ cap.length))) cap next) := by
    simp [indexStep,lookupState,unpairB_pairB,sel,next]
  by_cases ht : next.length ≤ cap.length
  · refine ⟨next,by simpa [← hlen] using (min_eq_right ht).symm,?_⟩
    rw [hstate]
    have yes : bflag (decide (next.length ≤ cap.length)) = [true] := by simp [ht,bflag]
    simp [yes,sel]
  · refine ⟨cap,by rw [← hlen,min_eq_left (by omega)],?_⟩
    rw [hstate]
    have no : bflag (decide (next.length ≤ cap.length)) = [] := by simp [ht,bflag]
    simp [no,sel]

private theorem indexIteration (cap bits index : Word) (fuel : Nat)
    (hf : bits.length ≤ fuel) (hi : index.length ≤ cap.length) :
    ∃ i : Word, i.length = min cap.length (bits.foldl binaryStep index.length) ∧
      indexStep^[fuel] (lookupState cap bits index) = lookupState cap [] i := by
  induction fuel generalizing bits index with
  | zero =>
    have he : bits = [] := List.length_eq_zero_iff.mp (by omega)
    subst bits
    exact ⟨index,by simp [min_eq_right hi],rfl⟩
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    cases bits with
    | nil =>
      have hfix : indexStep (lookupState cap [] index) = lookupState cap [] index := by
        simp [indexStep,lookupState,unpairB_pairB]
      rw [hfix]
      exact ih [] index (by simp) hi
    | cons b bits =>
      obtain ⟨i,hlen,he⟩ := indexStep_clip cap index b bits
      rw [he]
      obtain ⟨j,hj,hs⟩ := ih bits i (by simpa using hf) (hlen.trans_le (Nat.min_le_left _ _))
      have hfold (ys : Word) (a : Nat) :
          min cap.length (ys.foldl binaryStep (min cap.length a)) =
            min cap.length (ys.foldl binaryStep a) := by
        induction ys generalizing a with
        | nil => simp
        | cons d ys next =>
          simp only [List.foldl_cons]
          rw [← next (binaryStep (min cap.length a) d), clip_step, next (binaryStep a d)]
      refine ⟨j,?_,hs⟩
      simpa only [hlen,List.foldl_cons,hfold] using hj

def clippedIndex (bits table : Word) : Word :=
  (unpairB (unpairB (indexStep^[bits.length] (lookupState table bits []))).2).2

theorem clippedIndex_cpt :
    ComputableInPolyTime encodePair (fun x => x) (fun p : Word × Word => clippedIndex p.1 p.2) := by
  obtain ⟨c⟩ := indexStep_cpt
  have h := Iter.iter_polyTime_measure indexStep c indexMeasure 2 indexMeasure_step indexStep_size
    (fun s => by have hs := unpairB_length s; unfold indexMeasure; omega)
  have hi := cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const []))
  have hraw := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_comp (cpt_pair hi cpt_unpairB1) h))
  exact cpt_fromRaw (f := fun p : Word × Word => clippedIndex p.1 p.2) hraw

theorem clippedIndex_length (bits table : Word) :
    (clippedIndex bits table).length = min table.length (bits.foldl binaryStep 0) := by
  obtain ⟨i,hi,h⟩ := indexIteration table bits [] bits.length le_rfl (by simp)
  unfold clippedIndex
  rw [h]
  simpa [lookupState,unpairB_pairB] using hi

private theorem tailIter (i : Nat) (w : Word) : (fun x : Word => x.tail)^[i] w = w.drop i := by
  induction i generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,ih]
    cases w <;> simp

private theorem clipped_parts (bits table : Word) :
    table.take (clippedIndex bits table).length = table.take (bits.foldl binaryStep 0) ∧
    table.drop (clippedIndex bits table).length = table.drop (bits.foldl binaryStep 0) := by
  rw [clippedIndex_length]
  by_cases enough : bits.foldl binaryStep 0 ≤ table.length
  · rw [min_eq_right enough]
    exact ⟨rfl,rfl⟩
  · have h := Nat.le_of_not_ge enough
    rw [min_eq_left h]
    simp [List.take_of_length_le h, List.drop_eq_nil_of_le h]

/-- Read or split a Boolean table at the binary index encoded most significant
bit first. Index accumulation saturates at the table length, guaranteeing
polynomial time even when the raw index greatly exceeds the table length. -/
theorem MeasuredTruthTableLookup :
    ∃ (look : Word × Word → Bool) (split : Word × Word → Word),
      ComputableInPolyTime encodePair Computability.encodeBool look ∧
      ComputableInPolyTime encodePair (fun x => x) split ∧
      ∀ bits table : Word,
        let i := bits.foldl (fun a b => 2*a+b.toNat) 0
        let pack := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        look (bits,table) = (table.drop i).headD false ∧
        split (bits,table) = pack (table.take i) (table.drop i) := by
  let look := fun p : Word × Word =>
    (p.2.drop (clippedIndex p.1 p.2).length).headD false
  let split := fun p : Word × Word =>
    let i := (clippedIndex p.1 p.2).length
    pairB (p.2.take i) (p.2.drop i)
  have hi := cpt_comp cpt_unpairB clippedIndex_cpt
  have hDrop := cpt_iterLen cpt_tail (fun w => by simp) hi cpt_unpairB2
  have hTake := PEqualNP.Library.SearchHelpers.Tab.StepW.cpt_tk hi cpt_unpairB2
  have hr := cpt_comp hDrop wordHead_polyTime
  have hc : ComputableInPolyTime encodePair Computability.encodeBool look := by
    apply cpt_fromRawBool (f := look)
    exact bf_cptl hr (fun s => by simp [look,tailIter])
  have hs : ComputableInPolyTime encodePair (fun x => x) split := by
    apply cpt_fromRaw (f := split)
    refine bf_cptl (cpt_pairB2 hTake hDrop) (fun s => ?_)
    simp [split,tailIter,PEqualNP.Library.SearchHelpers.Tab.StepW.tk_eq]
  refine ⟨look,split,hc,hs,fun bits table => ?_⟩
  obtain ⟨h₁,h₂⟩ := clipped_parts bits table
  exact ⟨congrArg (fun x : Word => x.headD false) h₂,congrArg₂ pairB h₁ h₂⟩

end PEqualNP.Outside
