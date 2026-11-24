import PEqualNP.Outside.RecordPrefixQueries
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside.RecordMapMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.RecordPairScan (wire wire_len)
open PEqualNP.Outside.RecordPrefixQueries (wire_append)
open PEqualNP.Library.SearchHelpers.Tab.StepW (cpt_flatMapRange)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def tailRecord (w : Word) : Word := (unpairB w).2

theorem tailRecord_size (w : Word) : (tailRecord w).length ≤ w.length := by
  have h := unpairB_length w
  unfold tailRecord
  omega

def atIndex (f : Word → Word) (z : Word) : Word :=
  let r := tailRecord^[(unpairB z).1.length] (unpairB z).2
  sel r [] (f (unpairB r).1)

theorem atIndex_cpt (f : Word → Word) (hf : CPT f) : CPT (atIndex f) := by
  have hi : CPT (fun z => tailRecord^[(unpairB z).1.length] (unpairB z).2) :=
    cpt_iterLen cpt_unpairB2 tailRecord_size cpt_unpairB1 cpt_unpairB2
  exact cptl (cpt_sel hi (cpt_const [])
    (cpt_comp (cpt_unpairB1_1 hi) hf)) (fun _ => rfl)

def flatMapWord (f : Word → Word) (w : Word) : Word :=
  (List.range w.length).flatMap (fun i => atIndex f (pairB (un i) w))

theorem flatMapWord_cpt (f : Word → Word) (hf : CPT f) : CPT (flatMapWord f) :=
  cpt_flatMapRange (atIndex_cpt f hf) cpt_id cpt_id

theorem index_zero (f : Word → Word) (a : Word) (as : List Word) :
    atIndex f (pairB (un 0) (wire (a :: as))) = f a := by
  have hn : pairB a (wire as) ≠ [] := by simp [pairB]
  simp [atIndex, wire, unpairB_pairB, sel, hn, un_length]

theorem index_succ (f : Word → Word) (i : ℕ) (a : Word) (as : List Word) :
    atIndex f (pairB (un (i+1)) (wire (a :: as))) =
      atIndex f (pairB (un i) (wire as)) := by
  simp only [atIndex, unpairB_pairB, un_length, Function.iterate_succ_apply, wire, tailRecord]

theorem index_nil (f : Word → Word) (i : ℕ) :
    atIndex f (pairB (un i) (wire [])) = [] := by
  have hl : tailRecord [] = [] := rfl
  simp [atIndex, wire, unpairB_pairB, Function.iterate_fixed hl, sel]

theorem flatMap_enc (f : Word → Word) (F : Word → List Word)
    (hc : ∀ x, f x = wire (F x)) (n : ℕ) (as : List Word) (h : as.length ≤ n) :
    ((List.range n).flatMap (fun i => atIndex f (pairB (un i) (wire as)))) =
      wire (as.flatMap F) := by
  induction n generalizing as with
  | zero =>
    have he : as = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst as
    rfl
  | succ n ih =>
    cases as with
    | nil =>
      simp only [List.flatMap_nil, wire, List.flatMap_eq_nil_iff]
      intro i _
      exact index_nil f i
    | cons a as =>
      rw [List.range_succ_eq_map, List.flatMap_cons, index_zero, List.flatMap_map]
      simp only [Function.comp_apply, Nat.succ_eq_add_one, index_succ]
      rw [ih as (by simpa using h), hc, List.flatMap_cons, wire_append]

theorem flatMapWord_enc (f : Word → Word) (F : Word → List Word)
    (h : ∀ x, f x = wire (F x)) (as : List Word) :
    flatMapWord f (wire as) = wire (as.flatMap F) :=
  flatMap_enc f F h _ as (wire_len as)

def mapWord (f : Word → Word) : Word → Word := flatMapWord (fun x => pairB (f x) [])

theorem mapWord_cpt (f : Word → Word) (hf : CPT f) : CPT (mapWord f) :=
  flatMapWord_cpt _ (cpt_pairB2 hf (cpt_const []))

theorem mapWord_enc (f : Word → Word) (as : List Word) :
    mapWord f (wire as) = wire (as.map f) := by
  unfold mapWord
  rw [flatMapWord_enc (fun x => pairB (f x) []) (fun x => [f x]) (fun _ => rfl) as]
  congr 1
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

end PEqualNP.Outside.RecordMapMachine
