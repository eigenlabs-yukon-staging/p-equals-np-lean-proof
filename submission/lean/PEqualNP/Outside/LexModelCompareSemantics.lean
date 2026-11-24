import PEqualNP.Outside.LexModelCompareCore
import PEqualNP.Outside.LexModelItems
import PEqualNP.Outside.LexModelGateFacts

namespace PEqualNP.Outside.LexModelCompareSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.FirstWideCollector (Word rest count buf out pack)
open PEqualNP.Outside.LexModelCompareCore
open PEqualNP.Outside.LexModelItems (Item itemCode items items_enc items_count bits bits_enc)
open PEqualNP.Outside.LexModelGateFacts (less)

def diff : Word → Word → Option Bool
  | a :: as, b :: bs => if a = b then diff as bs else some b
  | _, _ => none

def flag : Option Bool → Word
  | none => []
  | some b => [b]

theorem diff_correct {as bs : Word} (h : as.length = bs.length) :
    diff as bs = some true ↔ List.Lex less as bs := by
  induction as generalizing bs with
  | nil =>
    have he : bs = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    subst bs
    constructor
    · simp [diff]
    · intro h
      cases h
  | cons a as ih =>
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil
      (l := bs) (by intro he; simp [he] at h)
    have he : as.length = bs.length := by simpa using h
    cases a <;> cases b
    · rw [show diff (false :: as) (false :: bs) = diff as bs by simp [diff], ih he]
      constructor
      · exact List.Lex.cons
      · intro h
        cases h with
        | rel h => simp [less] at h
        | cons h => exact h
    · exact ⟨fun _ => List.Lex.rel ⟨rfl, rfl⟩, fun _ => rfl⟩
    · constructor
      · simp [diff]
      · intro h
        cases h with
        | rel h => simp [less] at h
    · rw [show diff (true :: as) (true :: bs) = diff as bs by simp [diff], ih he]
      constructor
      · exact List.Lex.cons
      · intro h
        cases h with
        | rel h => simp [less] at h
        | cons h => exact h

theorem step_locked (r a b f : Word) (hn : f ≠ []) : step (pack r a b f) = pack r a b f := by
  simp [step, out, pack, unpairB_pairB, sel, hn]

theorem step_end (a b : Word) : step (pack [] a b []) = pack [] a b [] := by
  simp [step, rest, out, pack, unpairB_pairB, sel]

theorem step_close (a b r : Word) : step (pack ([false, false] ++ r) a b []) = pack r a b [] := by
  simp [step, rest, count, buf, out, pack, unpairB_pairB, sel, isEnd, bflag, dropI]

theorem step_lit (a b r : Word) (l : Literal) :
    step (pack (encodeLiteral l ++ r) a b []) =
      pack r a b (delta (asg a l.1) (asg b l.1)) := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, rest, count, buf, out, pack, unpairB_pairB, sel, hn, isEnd_lit, bflag,
    Bool.false_eq_true, ite_false, dropI_lit, headI_lit]
  simp [encodeLiteral_eq, asg]

theorem scan (a b : Word) (ts : List Item) :
    let z := step^[ts.length] (pack (ts.flatMap itemCode) a b [])
    match diff (bits (asg a) ts) (bits (asg b) ts) with
    | none => z = pack [] a b []
    | some value => ∃ r, z = pack r a b [value] := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons]
    cases t with
    | none =>
      simpa only [itemCode, step_close, bits, List.filterMap_cons, Option.map_none] using ih
    | some l =>
      simp only [itemCode, step_lit, bits, List.filterMap_cons, Option.map_some, diff]
      by_cases h : asg a l.1 = asg b l.1
      · simpa only [bits, delta, h, ite_true] using ih
      · simp only [delta, h, ite_false, Function.iterate_fixed
          (step_locked _ _ _ [asg b l.1] (by simp))]
        exact ⟨_, rfl⟩

theorem output_enc (φ : CNF) (a b : Word) :
    output (encodeCNF φ) (pairB a b) =
      flag (diff (LexModelGateFacts.bits (asg a) φ) (LexModelGateFacts.bits (asg b) φ)) := by
  have h := scan a b (items φ)
  rw [items_enc, items_count, bits_enc, bits_enc] at h
  change (match diff (LexModelGateFacts.bits (asg a) φ) (LexModelGateFacts.bits (asg b) φ) with
        | none => _ = _
        | some value => ∃ r, _ = pack r a b [value]) at h
  have hn := nIt_le φ
  unfold output
  rw [unpairB_pairB]
  dsimp only
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  cases hs : diff (LexModelGateFacts.bits (asg a) φ) (LexModelGateFacts.bits (asg b) φ) with
  | none =>
    simp only [hs] at h
    rw [h, Function.iterate_fixed (step_end a b)]
    simp [flag, pack, out, unpairB_pairB]
  | some value =>
    simp only [hs] at h
    obtain ⟨r, he⟩ := h
    rw [he, Function.iterate_fixed (step_locked _ _ _ [value] (by simp))]
    simp [flag, pack, out, unpairB_pairB]

theorem compare_correct (φ : CNF) (a b : Word) :
    output (encodeCNF φ) (pairB a b) = [true] ↔
      List.Lex less (LexModelGateFacts.bits (asg a) φ) (LexModelGateFacts.bits (asg b) φ) := by
  rw [output_enc, ← diff_correct (by simp only [LexModelGateFacts.bits, List.length_map])]
  cases h : diff (LexModelGateFacts.bits (asg a) φ) (LexModelGateFacts.bits (asg b) φ) with
  | none => simp [flag]
  | some b => cases b <;> simp [flag]

end PEqualNP.Outside.LexModelCompareSemantics
