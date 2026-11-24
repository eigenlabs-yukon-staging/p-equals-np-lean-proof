import PEqualNP.Outside.SparseImagePruneMachine
import PEqualNP.Outside.RecordMapMachine
import PEqualNP.Outside.RecordAttachQuery

namespace PEqualNP.Outside.SparseBoundedListPruning

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_cpt cut_eq)
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.RecordMapMachine (tailRecord tailRecord_size mapWord mapWord_cpt mapWord_enc)
open PEqualNP.Outside.RecordAttachQuery (attach attach_cpt attach_enc)
open PEqualNP.Outside.SparseImagePruneMachine (execute execute_cpt execute_enc records)
open PEqualNP.Outside.SparseImageCandidatePruning (prune prune_sublist prune_preserves)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)
local notation "CPT₂" => ComputableInPolyTime encodePair (fun x : Word => x)

def addImage (f : Word × Word → Word) (z : Word) : Word :=
  pairB (unpairB z).2 (f (unpairB z))

theorem addImage_cpt (f : Word × Word → Word) (hf : CPT₂ f) : CPT (addImage f) := by
  have hg := cpt_comp cpt_unpairB hf
  exact cptl (cpt_pairB2 cpt_unpairB2 hg) (fun _ => rfl)

def shrink (f : Word × Word → Word) (rs : Word) : Word :=
  let a := unpairB rs
  execute (a.1, mapWord (addImage f) (attach a))

theorem shrink_cpt (f : Word × Word → Word) (hf : CPT₂ f) : CPT (shrink f) := by
  have hm := cpt_comp (cpt_comp cpt_unpairB attach_cpt) (mapWord_cpt _ (addImage_cpt f hf))
  exact cptl (cpt_comp (cpt_pair cpt_unpairB1 hm) execute_cpt) (fun _ => rfl)

theorem shrink_enc (f : Word × Word → Word) (pivot : Word) (as : List Word) :
    shrink f (wire (pivot :: as)) = wire (prune pivot (as.map (fun x => (x,f (pivot,x))))) := by
  rw [wire]
  simp only [shrink,unpairB_pairB,attach_enc,mapWord_enc]
  simpa only [records,List.map_map,Function.comp_def,addImage,unpairB_pairB] using
    execute_enc pivot (as.map (fun x => (x,f (pivot,x))))

theorem wire_sublist {as bs : List Word} (h : as.Sublist bs) : (wire as).length ≤ (wire bs).length := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    rw [wire, pairB_length]
    omega
  | cons_cons a h ih =>
    rw [wire, wire, pairB_length, pairB_length]
    omega

theorem tailRecord_wire (n : ℕ) (as : List Word) :
    tailRecord^[n] (wire as) = wire (as.drop n) := by
  induction n generalizing as with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases as with
    | nil =>
      simp only [List.drop_nil]
      change tailRecord^[n] (wire ([] : List Word)) = wire []
      simpa only [List.drop_nil] using ih ([] : List Word)
    | cons a as => simp [tailRecord,wire,unpairB_pairB,ih]

theorem wire_empty (as : List Word) : wire as = [] ↔ as = [] := by
  cases as <;> simp [wire,pairB]

def trimStep (f : Word × Word → Word) (z : Word) : Word :=
  let q := unpairB z
  let excess := tailRecord^[q.1.length] q.2
  sel excess z (pairB q.1 (cut q.2 (shrink f q.2)))

theorem trimStep_cpt (f : Word × Word → Word) (hf : CPT₂ f) : CPT (trimStep f) := by
  have h := cpt_iterLen cpt_unpairB2 tailRecord_size cpt_unpairB1 cpt_unpairB2
  have hk := cut_cpt cpt_unpairB2 (cpt_comp cpt_unpairB2 (shrink_cpt f hf))
  exact cptl (cpt_sel h cpt_id (cpt_pairB2 cpt_unpairB1 hk)) (fun _ => rfl)

theorem trimStep_size (f : Word × Word → Word) (z : Word) :
    (trimStep f z).length ≤ z.length + 1 := by
  have h := unpairB_length z
  have hc : (cut (unpairB z).2 (shrink f (unpairB z).2)).length ≤ (unpairB z).2.length := by
    simp [cut_eq]
  simp only [trimStep, sel]
  split
  · omega
  · rw [pairB_length]
    omega

def stepList (f : Word × Word → Word) (cap : ℕ) (as : List Word) : List Word :=
  if as.length ≤ cap then as else
    match as with
    | [] => []
    | pivot :: bs => prune pivot (bs.map (fun x => (x,f (pivot,x))))

theorem trimStep_enc (f : Word × Word → Word) (cap : Word) (as : List Word) :
    trimStep f (pairB cap (wire as)) = pairB cap (wire (stepList f cap.length as)) := by
  simp only [trimStep, unpairB_pairB, sel, tailRecord_wire, wire_empty, List.drop_eq_nil_iff]
  by_cases h : as.length ≤ cap.length
  · simp [stepList,h]
  · cases as with
    | nil => simp at h
    | cons pivot bs =>
      simp only [h, ite_false, stepList]
      rw [shrink_enc]
      have hs := (prune_sublist pivot (bs.map (fun x => (x,f (pivot,x))))).1
      rw [List.map_map, show Prod.fst ∘ (fun x => (x,f (pivot,x))) = id by rfl, List.map_id] at hs
      rw [cut_eq, List.take_of_length_le (wire_sublist hs)]

theorem stepList_sublist (f : Word × Word → Word) (cap : ℕ) (as : List Word) :
    (stepList f cap as).Sublist as := by
  unfold stepList
  split
  · exact List.Sublist.refl _
  · cases as with
    | nil => exact List.Sublist.refl _
    | cons pivot bs =>
      simpa only [List.map_map, show Prod.fst ∘ (fun x => (x,f (pivot,x))) = id by rfl,
        List.map_id] using (prune_sublist pivot (bs.map (fun x => (x,f (pivot,x))))).1

theorem stepList_size (f : Word × Word → Word) (cap : ℕ) (as : List Word) :
    (stepList f cap as).length ≤ max cap (as.length-1) := by
  unfold stepList
  split
  · omega
  · cases as with
    | nil => simp
    | cons pivot bs =>
      have hs := (prune_sublist pivot (bs.map (fun x => (x,f (pivot,x))))).2
      simp only [List.length_cons, List.length_map] at *
      omega

theorem stepList_correct (f : Word × Word → Word) (G : Word → Prop) (S : Finset Word)
    (cap : ℕ) (hcap : S.card < cap) (as : List Word)
    (hrel : ∀ x ∈ as, ∀ y ∈ as, f (x,y) ∈ S ↔ G x ∨ G y) :
    (∃ x ∈ stepList f cap as, G x) ↔ ∃ x ∈ as, G x := by
  unfold stepList
  split
  · rfl
  · rename_i hover
    cases as with
    | nil => rfl
    | cons pivot bs =>
      have hl : S.card < (bs.map (fun x => (x,f (pivot,x)))).length := by
        simp only [List.length_map, List.length_cons] at *
        omega
      have hr : ∀ q ∈ bs.map (fun x => (x,f (pivot,x))), q.2 ∈ S ↔ G pivot ∨ G q.1 := by
        intro q hq
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hq
        exact hrel pivot List.mem_cons_self y (List.mem_cons_of_mem _ hy)
      simpa [List.exists_mem_cons_iff] using
        prune_preserves G S pivot (bs.map (fun x => (x,f (pivot,x)))) hl hr

def trim (f : Word × Word → Word) (q : Word × Word) : Word :=
  (unpairB ((trimStep f)^[q.2.length] (pairB q.1 q.2))).2

theorem trim_cpt (f : Word × Word → Word) (hf : CPT₂ f) : CPT₂ (trim f) := by
  obtain ⟨m⟩ := trimStep_cpt f hf
  have hlo := Iter.iter_polyTime (trimStep f) m 1 (trimStep_size f)
  exact cptl (cpt_comp (cpt_comp (cpt_pairG cpt_pairB cpt_snd) hlo) cpt_unpairB2) (fun _ => rfl)

theorem trim_loop (f : Word × Word → Word) (cap : Word) (n : ℕ) (as : List Word) :
    (trimStep f)^[n] (pairB cap (wire as)) = pairB cap (wire ((stepList f cap.length)^[n] as)) := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, trimStep_enc, ih, Function.iterate_succ_apply]

theorem iterate_list (f : Word × Word → Word) (G : Word → Prop) (S : Finset Word)
    (cap : ℕ) (hcap : S.card < cap) (n : ℕ) (as : List Word)
    (hrel : ∀ x ∈ as, ∀ y ∈ as, f (x,y) ∈ S ↔ G x ∨ G y) :
    let bs := (stepList f cap)^[n] as
    bs.Sublist as ∧ bs.length ≤ max cap (as.length-n) ∧
      ((∃ x ∈ bs, G x) ↔ ∃ x ∈ as, G x) := by
  induction n generalizing as with
  | zero => exact ⟨List.Sublist.refl _, by simp, Iff.rfl⟩
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    have hsub := stepList_sublist f cap as
    have hs := stepList_size f cap as
    have hc := stepList_correct f G S cap hcap as hrel
    obtain ⟨hu,hb,he⟩ := ih (stepList f cap as)
      (fun x hx y hy => hrel x (hsub.subset hx) y (hsub.subset hy))
    exact ⟨hu.trans hsub, by omega, he.trans hc⟩

theorem trim_correct (f : Word × Word → Word) (G : Word → Prop) (S : Finset Word)
    (cap : Word) (hcap : S.card < cap.length) (as : List Word)
    (hrel : ∀ x ∈ as, ∀ y ∈ as, f (x,y) ∈ S ↔ G x ∨ G y) :
    ∃ bs : List Word, trim f (cap,wire as) = wire bs ∧
      bs.Sublist as ∧ bs.length ≤ cap.length ∧ ((∃ x ∈ bs, G x) ↔ ∃ x ∈ as, G x) := by
  let bs := (stepList f cap.length)^[(wire as).length] as
  obtain ⟨hs,hl,he⟩ := iterate_list f G S cap.length hcap (wire as).length as hrel
  refine ⟨bs,?_,hs,?_,he⟩
  · simp only [trim, trim_loop, unpairB_pairB, bs]
  · simpa only [Nat.sub_eq_zero_of_le (wire_len as), Nat.max_zero] using hl

end PEqualNP.Outside.SparseBoundedListPruning

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.SparseBoundedListPruning (trim trim_cpt trim_correct)

theorem PEqualNP.Outside.SparseBoundedListPruning :
    ∀ f : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x => x) f →
      ∃ (E : List (List Bool) → List Bool) (F : List Bool × List Bool → List Bool),
        E [] = [] ∧
        (∀ a as, E (a :: as) = List.replicate a.length true ++ false :: (a ++ E as)) ∧
        ComputableInPolyTime encodePair (fun w => w) F ∧
        ∀ (G : List Bool → Prop) (S : Finset (List Bool)) (cap : List Bool) (as : List (List Bool)),
          S.card < cap.length →
          (∀ x ∈ as, ∀ y ∈ as, f (x,y) ∈ S ↔ G x ∨ G y) →
          ∃ bs : List (List Bool), F (cap,E as) = E bs ∧
            bs.Sublist as ∧ bs.length ≤ cap.length ∧ ((∃ x ∈ bs, G x) ↔ ∃ x ∈ as, G x) := by
  intro f hf
  refine ⟨wire,trim f,rfl,fun _ _ => rfl,trim_cpt f hf,?_⟩
  intro G S cap as hc he
  exact trim_correct f G S cap hc as he
