import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def withoutVar (i : ℕ) (c : Clause) : Clause := c.filter (fun l => decide (l.1 ≠ i))

private def keep (mode : Option Bool) (i : ℕ) (c : Clause) : Bool :=
  mode.elim true (fun b => decide ((i,b) ∉ c))

private theorem encode_cons (l : Literal) (c : Clause) :
    encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]

private theorem formula_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]

private theorem drop_nil (n : ℕ) : dropI^[n] ([] : List Bool) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,show dropI [] = [] by rfl,ih]

private theorem drop_encoded (c : Clause) (i : ℕ) :
    dropI^[i] (encodeClause c) = if i ≤ c.length then encodeClause (c.drop i) else [] := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases c with
    | nil => exact drop_nil i
    | cons l c =>
        rw [encode_cons,dropI_lit,ih]
        simp

private theorem clause_count (c : Clause) : c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      rw [encode_cons,List.length_append,List.length_cons]
      have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega

private theorem formula_count (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [formula_cons,List.length_append,List.length_cons]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

private theorem lit_code_inj {l m : Literal} (h : encodeLiteral l = encodeLiteral m) : l = m := by
  exact (PEqualNP.Library.SearchHelpers.literal_append_inj l m [] [] (by simpa using h)).1

private theorem same_code (i j : ℕ) : vcode i = vcode j ↔ i = j :=
  ⟨fun h => vcode_injective h,congrArg vcode⟩

theorem literal_mem_code (l : Literal) (c : Clause) :
    memB (encodeLiteral l) (encodeClause c) = true ↔ l ∈ c := by
  rw [memB_iff]
  constructor
  · rintro ⟨i,_,hi⟩
    rw [drop_encoded] at hi
    by_cases h : i < c.length
    · rw [ite_eq_left h.le,List.drop_eq_getElem_cons h,encode_cons,headI_lit] at hi
      have he := lit_code_inj hi
      exact he ▸ List.getElem_mem h
    · have hle : c.length ≤ i := by omega
      by_cases e : i ≤ c.length
      · rw [ite_eq_left e,List.drop_eq_nil_iff.mpr hle] at hi
        simp [headI,encodeClause,encodeLiteral] at hi
      · rw [ite_eq_right e] at hi
        simp [headI,encodeLiteral] at hi
  · intro h
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
    refine ⟨i,hi.trans_le (clause_count c),?_⟩
    rw [drop_encoded,ite_eq_left hi.le,List.drop_eq_getElem_cons hi,encode_cons,headI_lit,he]

private def filteredItem (v w : List Bool) : List Bool :=
  if w.headD false then
    if (headI w).tail.tail = v then [] else headI w
  else []

private theorem filter_range (var : ℕ) (c : Clause) (n : ℕ) (hn : c.length ≤ n) :
    (List.range n).flatMap (fun i => filteredItem (vcode var) (dropI^[i] (encodeClause c))) =
      (withoutVar var c).flatMap encodeLiteral := by
  induction c generalizing n with
  | nil =>
      have he (i : ℕ) : filteredItem (vcode var) (dropI^[i] (encodeClause [])) = [] := by
        rw [drop_encoded]
        cases i <;> rfl
      change _ = ([] : List Bool)
      rw [List.flatMap_eq_nil_iff]
      exact fun i _ => he i
  | cons l c ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have ht : c.length ≤ n := by simpa using hn
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          have he (i : ℕ) :
              dropI^[i+1] (encodeClause (l :: c)) = dropI^[i] (encodeClause c) := by
            rw [Function.iterate_succ_apply,encode_cons,dropI_lit]
          simp only [Function.comp_apply,he,Function.iterate_zero_apply]
          rw [ih n ht,filteredItem,encode_cons,headI_lit]
          have hs : (encodeLiteral l ++ encodeClause c).headD false = true := rfl
          simp only [hs,ite_true,encodeLiteral_eq,List.tail_cons,same_code,withoutVar,List.filter_cons]
          by_cases h : l.1 = var <;> simp [h,encodeLiteral_eq]

private theorem measured_omit :
    ∃ filter : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) filter ∧
      ∀ var : ℕ, ∀ c : Clause, filter (vcode var,encodeClause c) = encodeClause (withoutVar var c) := by
  let r := fun s => dropI^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r :=
    cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let v := fun s => (unpairB (unpairB s).2).1
  have hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v :=
    cpt_unpairB1_1 cpt_unpairB2
  let branch := fun s => filteredItem (v s) (r s)
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) branch := by
    have hi := cpt_comp hr cpt_headI
    have flag := cpt_eqF (cpt_tail1 (cpt_tail1 hi)) hv
    refine cptE (cpt_sel (cpt_hd1 hr) (cpt_const []) (cpt_sel flag hi (cpt_const []))) (fun s => ?_)
    unfold branch filteredItem
    rcases r s with _ | ⟨b,rest⟩
    · rfl
    · cases b with
      | false => rfl
      | true =>
          by_cases he : (headI (true :: rest)).tail.tail = v s <;> simp [sel,hd,bflag,he]
  let raw := fun s => ((List.range (unpairB s).2.length).flatMap (fun i => branch (pairB (un i) s))) ++ [false,false]
  have hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_app2 (cpt_flatMapRange hb cpt_unpairB2 cpt_id) (cpt_const [false,false])
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp (g := raw) cpt_pairB hm,fun i c => ?_⟩
  simp only [raw,branch,r,v,unpairB_pairB,un_length]
  rw [filter_range i c _ (clause_count c)]
  rfl

private theorem measured_guard (mode : Option Bool) :
    ∃ passes : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) passes ∧
      ∀ (i : ℕ) (c : Clause), passes (vcode i,encodeClause c) = bflag (!keep mode i c) := by
  cases mode with
  | none =>
      exact ⟨fun _ => [],cpt_comp cpt_fst (cpt_const []),fun i c => rfl⟩
  | some b =>
      let mk := fun s => true :: b :: (unpairB s).1
      have hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mk :=
        cpt_cons1 true (cpt_cons1 b cpt_unpairB1)
      have h := cpt_memB hm cpt_unpairB2
      refine ⟨fun p => bflag (memB (true :: b :: p.1) p.2),?_,?_⟩
      · have h' := cpt_comp cpt_pairB h
        have he : (fun p : List Bool × List Bool =>
            bflag (memB (mk (pairB p.1 p.2)) (unpairB (pairB p.1 p.2)).2)) =
            (fun p => bflag (memB (true :: b :: p.1) p.2)) := by
          funext p
          simp only [mk,unpairB_pairB]
        rwa [he] at h'
      · intro i c
        change bflag (memB (true :: b :: vcode i) (encodeClause c)) = _
        rw [show true :: b :: vcode i = encodeLiteral (i,b) from rfl]
        have he := literal_mem_code (i,b) c
        by_cases hb : (i,b) ∈ c
        · simp [he.mpr hb,keep,hb]
        · have hf := Bool.eq_false_iff.mpr (fun ht => hb (he.mp ht))
          simp [hf,keep,hb]

private theorem outer_range (split : List Bool → List Bool × List Bool)
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hz : (split []).2 = [])
    (out : List Bool → List Bool)
    (mode : Option Bool) (var : ℕ)
    (hout : ∀ c : Clause, out (encodeClause c) =
      if keep mode var c then encodeClause (withoutVar var c) else [])
    (φ : CNF) (n : ℕ) (hn : φ.length ≤ n) :
    (List.range n).flatMap (fun i =>
      let r := (fun s => (split s).2)^[i] (encodeCNF φ)
      if r = [] then [] else out (split r).1) =
      encodeCNF ((φ.filter (keep mode var)).map (withoutVar var)) := by
  induction φ generalizing n with
  | nil =>
      have he (i : ℕ) : (fun s => (split s).2)^[i] ([] : List Bool) = [] := by
        induction i with
        | zero => rfl
        | succ i ih => rw [Function.iterate_succ_apply,hz,ih]
      have hh : (List.range n).flatMap (fun i =>
          let r := (fun s => (split s).2)^[i] (encodeCNF [])
          if r = [] then [] else out (split r).1) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro i _
        change (if (fun s => (split s).2)^[i] ([] : List Bool) = [] then [] else _) = []
        rw [he]
        rfl
      rw [hh]
      rfl
  | cons c φ ih =>
      cases n with
      | zero => simp at hn
      | succ n =>
          have ht : φ.length ≤ n := by simpa using hn
          have hne : encodeCNF (c :: φ) ≠ [] := by rw [formula_cons]; simp [encodeClause]
          rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
          have hnext (i : ℕ) :
              (fun s => (split s).2)^[i+1] (encodeCNF (c :: φ)) =
                (fun s => (split s).2)^[i] (encodeCNF φ) := by
            rw [Function.iterate_succ_apply,formula_cons]
            simp only [hs]
          simp only [hnext,Function.iterate_zero_apply]
          change (if encodeCNF (c :: φ) = [] then [] else out (split (encodeCNF (c :: φ))).1) ++
            (List.range n).flatMap (fun i =>
              let r := (fun s => (split s).2)^[i] (encodeCNF φ)
              if r = [] then [] else out (split r).1) = _
          rw [ite_eq_right hne,formula_cons,hs,hout,ih n ht]
          cases h : keep mode var c <;> simp [h,formula_cons]

/-- Measured one-variable deletion or assignment restriction of a canonical CNF. -/
theorem MeasuredVariableRestriction (mode : Option Bool) :
    ∃ restrict : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) restrict ∧
      ∀ (i : ℕ) (φ : CNF),
        restrict ((i.bits.flatMap fun b => [true,b]) ++ [false,true],encodeCNF φ) =
          encodeCNF ((φ.filter (fun c => mode.elim true (fun b => decide ((i,b) ∉ c)))).map
            (fun c => c.filter (fun l => decide (l.1 ≠ i)))) := by
  obtain ⟨split,hs,hjoin,hsem⟩ := measuredFirstClause_reassembles
  obtain ⟨filter,hfilter,hf⟩ := measured_omit
  obtain ⟨passes,hpasses,hps⟩ := measured_guard mode
  let tail := fun s => (split s).2
  have ht : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) tail :=
    cpt_comp hs cpt_snd
  have hlen (s : List Bool) : (tail s).length ≤ s.length := by
    have h := congrArg List.length (hjoin s)
    simp only [List.length_append] at h
    dsimp only [tail]
    omega
  let r := fun s => tail^[(unpairB s).1.length] (unpairB (unpairB s).2).2
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r :=
    cpt_iterLen ht hlen cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)
  let branch := fun s => if r s = [] then [] else
    let p := ((unpairB (unpairB s).2).1,(split (r s)).1)
    sel (passes p) (filter p) []
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) branch := by
    have hp := cpt_pair (cpt_unpairB1_1 cpt_unpairB2) (cpt_comp (cpt_comp hr hs) cpt_fst)
    exact cpt_sel hr (cpt_const []) (cpt_sel (cpt_comp hp hpasses)
      (cpt_comp hp hfilter) (cpt_const []))
  let raw := fun s => (List.range (unpairB s).2.length).flatMap (fun i => branch (pairB (un i) s))
  have hraw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) raw :=
    cpt_flatMapRange hb cpt_unpairB2 cpt_id
  refine ⟨fun p => raw (pairB p.1 p.2),cpt_comp (g := raw) cpt_pairB hraw,fun i φ => ?_⟩
  change raw (pairB (vcode i) (encodeCNF φ)) = encodeCNF ((φ.filter (keep mode i)).map (withoutVar i))
  simp only [raw,branch,r,tail,unpairB_pairB,un_length]
  have hz : (split []).2 = [] := (List.append_eq_nil_iff.mp (hjoin [])).2
  have hbody (c : Clause) : sel (passes (vcode i,encodeClause c))
      (filter (vcode i,encodeClause c)) [] =
      if keep mode i c then encodeClause (withoutVar i c) else [] := by
    rw [hps,hf]
    cases keep mode i c <;> rfl
  exact outer_range split hsem hz (fun c => sel (passes (vcode i,c)) (filter (vcode i,c)) [])
    mode i hbody φ _ (formula_count φ)

end PEqualNP.Outside
