import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Library.Universal.BruteForce
import Mathlib.Data.Finset.Dedup

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Search

private abbrev Raw := List Bool

private def offList (p : Raw × Raw) : Raw := sel (bflag (memB p.2 p.1)) [true] []

private theorem offList_cpt : ComputableInPolyTime encodePair (fun x : Raw => x) offList := by
  change ComputableInPolyTime _ _ (fun p : Raw × Raw => sel (bflag (memB p.2 p.1)) [true] [])
  have h := cpt_sel (cpt_memB cpt_unpairB2 cpt_unpairB1) (cpt_const [true]) (cpt_const [])
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

private theorem subset_measured :
    ∃ test : Raw × Raw → Bool, ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ c d : Clause, test (encodeClause c,encodeClause d) = true ↔ c ⊆ d := by
  obtain ⟨scan,hs,hcs⟩ := MeasuredLiteralMap offList offList_cpt
  let r := fun p : Raw × Raw => scan (p.2,p.1)
  let test := fun p => (r p).isEmpty
  have hr := cpt_comp (cpt_pair cpt_unpairB2 cpt_unpairB1) hs
  have ht := cpt_comp (g := fun w : Raw => !w.isEmpty) (cpt_comp cpt_pairB
    (cpt_sel hr (cpt_const [true]) (cpt_const []))) bf_cpt_neL
  have he : (fun p : Raw × Raw => !(sel (r p) [true] []).isEmpty) = test := by
    funext p
    unfold test
    cases r p <;> rfl
  simp only [unpairB_pairB] at ht
  rw [he] at ht
  refine ⟨test,ht,fun c d => ?_⟩
  change (scan (encodeClause d,encodeClause c)).isEmpty = true ↔ _
  rw [List.isEmpty_iff,hcs,List.flatMap_eq_nil_iff]
  change (∀ l ∈ c, offList (encodeClause d,encodeLiteral l) = []) ↔ ∀ l ∈ c, l ∈ d
  apply forall_congr'
  intro l
  apply imp_congr_right
  intro _
  unfold offList
  rw [← literal_mem_code l d]
  cases memB (encodeLiteral l) (encodeClause d) <;> decide

/-- Exact finite-set equality on canonical clauses, ignoring ordering and
duplicate repetitions in the list encoding. -/
theorem MeasuredClauseSetEquality :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ c d : Clause, test (encodeClause c,encodeClause d) = true ↔ c.toFinset = d.toFinset := by
  obtain ⟨sub,hs,hss⟩ := subset_measured
  let test := fun p : Raw × Raw => sub p && sub (p.2,p.1)
  have h1 := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hs)
  have h2 := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB2 cpt_unpairB1) hs)
  have h := cpt_comp (g := fun w : Raw => !w.isEmpty)
    (cpt_comp cpt_pairB (cpt_sel h1 (cpt_const []) h2)) bf_cpt_neL
  have he :
      (fun p : Raw × Raw => !(sel (if sub p then [true] else []) []
        (if sub (p.2,p.1) then [true] else [])).isEmpty) = test := by
    funext p
    unfold test
    cases sub p <;> cases sub (p.2,p.1) <;> rfl
  simp only [unpairB_pairB] at h
  rw [he] at h
  refine ⟨test,h,fun c d => ?_⟩
  simp only [test,Bool.and_eq_true,hss]
  constructor
  · rintro ⟨hc,hd⟩
    apply Finset.Subset.antisymm
    · exact fun _ h => List.mem_toFinset.mpr (hc (List.mem_toFinset.mp h))
    · exact fun _ h => List.mem_toFinset.mpr (hd (List.mem_toFinset.mp h))
  · intro h
    constructor
    · exact fun l hl => List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr hl)
    · exact fun l hl => List.mem_toFinset.mp (h.symm ▸ List.mem_toFinset.mpr hl)

/-- Remove every occurrence of the selected literal while retaining the
encoded payload of the other literals without a clause delimiter. -/
theorem measuredLiteralPayloadErase :
    ∃ erase : Raw × Raw → Raw,
      ComputableInPolyTime encodePair (fun x : Raw => x) erase ∧
      ∀ (l : Literal) (c : Clause), erase (encodeLiteral l,encodeClause c) =
        (c.filter (fun m => decide (m ≠ l))).flatMap encodeLiteral := by
  let keep := fun z : Raw × Raw => sel (bflag (decide (z.2=z.1))) z.2 []
  have hc : ComputableInPolyTime encodePair (fun x : Raw => x) keep := by
    have h := cpt_sel (cpt_eqF cpt_unpairB2 cpt_unpairB1) cpt_unpairB2 (cpt_const [])
    simpa only [unpairB_pairB,keep] using cpt_comp cpt_pairB h
  obtain ⟨erase,he,hs⟩ := MeasuredLiteralMap keep hc
  refine ⟨erase,he,fun l c => ?_⟩
  rw [hs]
  have hk (m : Literal) : keep (encodeLiteral l,encodeLiteral m) =
      if m ≠ l then encodeLiteral m else [] := by
    have he : encodeLiteral m = encodeLiteral l ↔ m = l :=
      ⟨fun h => encodeLiteral_injective h,congrArg encodeLiteral⟩
    by_cases h : m = l <;> simp [keep,sel,bflag,he,h]
  simp only [hk]
  induction c with
  | nil => rfl
  | cons m c ih => by_cases he : m = l <;> simp [he] at ih ⊢ <;> exact ih

end PEqualNP.Outside
