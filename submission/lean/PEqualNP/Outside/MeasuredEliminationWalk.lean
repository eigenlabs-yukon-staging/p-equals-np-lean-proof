import PEqualNP.Outside.MeasuredCNFSubset
import PEqualNP.Outside.MeasuredDavisPutnamStep
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

theorem clauseSet_eq_empty_iff (φ : CNF) : clauseSet φ = ∅ ↔ φ = [] := by
  cases φ with
  | nil => simp [clauseSet]
  | cons c cs =>
    simp only [List.cons_ne_nil,iff_false]
    intro h
    have hm : c.toFinset ∈ clauseSet (c::cs) := ⟨c,List.mem_cons_self,rfl⟩
    rw [h] at hm
    exact hm

private abbrev Raw := List Bool
private abbrev Transform := Raw × Raw → Raw
private abbrev Test := Raw × Raw → Bool
private def pack (u order current ok : Raw) : Raw := pairB u (pairB order (pairB current ok))
private def ambient (s : Raw) := (unpairB s).1
private def todo (s : Raw) := (unpairB (unpairB s).2).1
private def current (s : Raw) := (unpairB (unpairB (unpairB s).2).2).1
private def valid (s : Raw) := (unpairB (unpairB (unpairB s).2).2).2

private theorem projections (u o c ok : Raw) :
    ambient (pack u o c ok) = u ∧ todo (pack u o c ok) = o ∧
    current (pack u o c ok) = c ∧ valid (pack u o c ok) = ok := by
  simp [ambient,todo,current,valid,pack,unpairB_pairB]

private def advance (elim intersect : Transform) (test : Test) (s : Raw) : Raw :=
  let next := elim (headI (todo s),current s)
  let rep := tk (ambient s) (intersect (next,ambient s))
  pack (ambient s) (dropI (todo s)) rep (bflag (test (next,ambient s)))

private def step (elim intersect : Transform) (test : Test) (s : Raw) : Raw :=
  sel (valid s) s (sel (hd (todo s)) s (advance elim intersect test s))

private theorem step_cpt {elim intersect : Transform} {test : Test}
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) elim)
    (hi : ComputableInPolyTime encodePair (fun x : Raw => x) intersect)
    (ht : ComputableInPolyTime encodePair Computability.encodeBool test) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (step elim intersect test) := by
  have hu := cpt_unpairB1
  have ho := cpt_unpairB1_1 cpt_unpairB2
  have hr := cpt_unpairB2_1 cpt_unpairB2
  have hc := cpt_unpairB1_1 hr
  have hv := cpt_unpairB2_1 hr
  have hn := cpt_comp (cpt_pair (cpt_comp ho cpt_headI) hc) he
  have hpair := cpt_pair hn hu
  have hp := cpt_tk hu (cpt_comp hpair hi)
  have hf := cpt_bitFlag (cpt_comp hpair ht)
  have ha := cpt_pairB2 hu (cpt_pairB2 (cpt_comp ho cpt_dropI) (cpt_pairB2 hp hf))
  exact cpt_sel hv cpt_id (cpt_sel (cpt_comp ho cpt_hd) cpt_id ha)

private def allowance (s : Raw) := 4*(ambient s).length + 4

private theorem advance_allowance (e i : Transform) (t : Test) (s : Raw) :
    allowance (advance e i t s) = allowance s := by
  dsimp only [allowance,advance]
  rw [(projections _ _ _ _).1]

private theorem step_allowance (e i : Transform) (t : Test) (s : Raw) :
    allowance (step e i t s) ≤ allowance s := by
  unfold step sel
  split
  · rfl
  · split
    · rfl
    · exact (advance_allowance e i t s).le

private theorem advance_length (e i : Transform) (t : Test) (s : Raw) :
    (advance e i t s).length ≤ s.length + allowance s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have hd := dropI_length (todo s)
  have hp := tk_length (ambient s) (i (e (headI (todo s),current s),ambient s))
  have hflag : (bflag (t (e (headI (todo s),current s),ambient s))).length ≤ 1 := by
    cases t (e (headI (todo s),current s),ambient s) <;> decide
  simp only [advance,pack,allowance,pairB_length,List.length_append]
  dsimp only [todo,ambient] at hd hp hflag ⊢
  omega

private theorem step_length (e i : Transform) (t : Test) (s : Raw) :
    (step e i t s).length ≤ s.length + allowance s := by
  unfold step sel
  split
  · omega
  · split
    · omega
    · exact advance_length e i t s

private theorem allowance_bound (s : Raw) : allowance s ≤ 4*s.length + 4 := by
  have h := unpairB_length s
  unfold allowance ambient
  omega


private def covered (U : Set NatClause) : List ℕ → Set NatClause → Prop
  | [], F => F ⊆ U
  | x :: xs, F => F ⊆ U ∧ covered U xs (eliminateVariable x F)

private theorem covered_iff (U : Set NatClause) (order : List ℕ) (F : Set NatClause) :
    covered U order F ↔
      ∀ j ≤ order.length, (order.take j).foldl (fun G x => eliminateVariable x G) F ⊆ U := by
  induction order generalizing F with
  | nil => simp [covered]
  | cons x order ih =>
    rw [covered,ih]
    constructor
    · rintro ⟨hF,hrest⟩ (j|j) hj
      · exact hF
      · exact hrest j (by simpa using hj)
    · intro h
      refine ⟨h 0 (Nat.zero_le _),fun j hj => ?_⟩
      exact h (j+1) (by simpa using hj)

private def orderCode (order : List ℕ) := encodeClause (order.map (fun x => (x,true)))

private def representative (φ U : CNF) : CNF :=
  U.filter (fun c => decide (∃ d ∈ φ, d.toFinset = c.toFinset))

private theorem representative_set (φ U : CNF) (h : clauseSet φ ⊆ clauseSet U) :
    clauseSet (representative φ U) = clauseSet φ := by
  ext c
  constructor
  · rintro ⟨d,hd,rfl⟩
    change ∃ z ∈ φ, z.toFinset = d.toFinset
    exact of_decide_eq_true (List.mem_filter.mp hd).2
  · intro hc
    obtain ⟨d,hd,rfl⟩ := h hc
    exact ⟨d,List.mem_filter.mpr ⟨hd,decide_eq_true (show ∃ d' ∈ φ, d'.toFinset = d.toFinset from hc)⟩,rfl⟩

private theorem rep_cap (φ U : CNF) :
    tk (encodeCNF U) (encodeCNF (representative φ U)) = encodeCNF (representative φ U) := by
  rw [tk_eq]
  apply List.take_of_length_le
  have h : (representative φ U).Sublist U := List.filter_sublist
  exact (h.flatMap encodeClause).length_le

private theorem step_frozen (e i : Transform) (t : Test) (u o c : Raw) :
    step e i t (pack u o c []) = pack u o c [] := by
  simp [step,(projections _ _ _ _).2.2.2,sel]

private theorem step_finished (e i : Transform) (t : Test) (u c ok : Raw) :
    step e i t (pack u (orderCode []) c ok) = pack u (orderCode []) c ok := by
  simp only [step,(projections _ _ _ _).2.1,(projections _ _ _ _).2.2.2]
  have hz : hd (orderCode []) = [] := rfl
  rw [hz]
  cases ok <;> rfl

private theorem advance_canonical (e i : Transform) (t : Test) (U φ ψ : CNF) (x : ℕ) (xs : List ℕ)
    (he : e (encodeLiteral (x,true),encodeCNF φ) = encodeCNF ψ)
    (hi : i (encodeCNF ψ,encodeCNF U) = encodeCNF (representative ψ U)) :
    step e i t (pack (encodeCNF U) (orderCode (x::xs)) (encodeCNF φ) [true]) =
      pack (encodeCNF U) (orderCode xs) (encodeCNF (representative ψ U))
        (bflag (t (encodeCNF ψ,encodeCNF U))) := by
  have hcode : orderCode (x::xs) = encodeLiteral (x,true) ++ orderCode xs := by
    simp [orderCode,encodeClause]
  have hhd : hd (orderCode (x::xs)) ≠ [] := by
    rw [hcode]
    simp [hd,encodeLiteral_eq]
  unfold step
  simp only [(projections _ _ _ _).2.2.2,(projections _ _ _ _).2.1,sel,hhd,List.cons_ne_nil,ite_false]
  simp only [advance,(projections _ _ _ _).1,(projections _ _ _ _).2.1,
    (projections _ _ _ _).2.2.1,hcode,headI_lit,dropI_lit,he,hi,rep_cap]

private theorem projection_frozen (e i : Transform) (t : Test) (u o c : Raw) (n : ℕ) :
    valid ((step e i t)^[n] (pack u o c [])) = [] := by
  induction n with
  | zero => exact (projections _ _ _ _).2.2.2
  | succ n ih => rw [Function.iterate_succ_apply,step_frozen,ih]

private theorem walk_spec (e i : Transform) (t : Test)
    (he : ∀ (x : ℕ) (φ : CNF), ∃ ψ : CNF, e (encodeLiteral (x,true),encodeCNF φ) = encodeCNF ψ ∧
      clauseSet ψ = eliminateVariable x (clauseSet φ))
    (hi : ∀ φ U : CNF, i (encodeCNF φ,encodeCNF U) = encodeCNF (representative φ U))
    (ht : ∀ φ U : CNF, t (encodeCNF φ,encodeCNF U) = true ↔ clauseSet φ ⊆ clauseSet U)
    (U φ : CNF) (order : List ℕ) (n : ℕ) (hlen : order.length ≤ n)
    (flag : Bool) (hflag : flag = true ↔ clauseSet φ ⊆ clauseSet U) :
    let result := (step e i t)^[n] (pack (encodeCNF U) (orderCode order) (encodeCNF φ) (bflag flag))
    (valid result = [true] ↔ covered (clauseSet U) order (clauseSet φ)) ∧
    (valid result = [true] → ∃ ψ : CNF, current result = encodeCNF ψ ∧
      clauseSet ψ = order.foldl (fun G x => eliminateVariable x G) (clauseSet φ)) := by
  dsimp only
  induction order generalizing n φ flag with
  | nil =>
    clear hlen
    have hfix : (step e i t)^[n] (pack (encodeCNF U) (orderCode []) (encodeCNF φ) (bflag flag)) =
        pack (encodeCNF U) (orderCode []) (encodeCNF φ) (bflag flag) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply,step_finished,ih]
    rw [hfix,(projections _ _ _ _).2.2.2,(projections _ _ _ _).2.2.1]
    exact ⟨by cases flag <;> simpa [covered,bflag] using hflag,fun _ => ⟨φ,rfl,rfl⟩⟩
  | cons x xs ih =>
    cases flag with
    | false =>
      rw [show bflag false = [] by rfl,projection_frozen]
      have hn : ¬ clauseSet φ ⊆ clauseSet U := fun h => Bool.noConfusion (hflag.mpr h)
      simp [covered,hn]
    | true =>
      cases n with
      | zero => simp at hlen
      | succ n =>
        obtain ⟨ψ,hcode,hset⟩ := he x φ
        have hcur := hflag.mp rfl
        rw [Function.iterate_succ_apply,show bflag true = [true] by rfl,advance_canonical e i t U φ ψ x xs hcode (hi ψ U)]
        by_cases hnext : clauseSet ψ ⊆ clauseSet U
        · have hp := representative_set ψ U hnext
          have hflag' : t (encodeCNF ψ,encodeCNF U) = true ↔ clauseSet (representative ψ U) ⊆ clauseSet U := by
            rw [hp,ht]
          have hs := ih (representative ψ U) n (by simpa using hlen) _ hflag'
          simpa only [covered,hcur,true_and,List.foldl_cons,hp,hset] using hs
        · have hfalse : t (encodeCNF ψ,encodeCNF U) = false :=
            Bool.eq_false_iff.mpr (fun h => hnext ((ht ψ U).mp h))
          have hn : ¬ covered (clauseSet U) xs (eliminateVariable x (clauseSet φ)) := by
            rw [← hset]
            cases xs <;> simp [covered,hnext]
          simp [hfalse,bflag,projection_frozen,covered,hcur,hn]


private theorem flag_shape (b : Bool) : bflag b = [] ∨ bflag b = [true] := by
  cases b <;> simp [bflag]

private theorem iterate_shape (e i : Transform) (t : Test) (s : Raw) (n : ℕ)
    (h : valid s = [] ∨ valid s = [true]) :
    valid ((step e i t)^[n] s) = [] ∨ valid ((step e i t)^[n] s) = [true] := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    unfold step sel
    split
    · exact ih
    · split
      · exact ih
      · simp only [advance,(projections _ _ _ _).2.2.2]
        exact flag_shape _

set_option maxHeartbeats 450000 in
/-- Verify every stage of a supplied elimination order in polynomial time,
returning a canonical final stage when every stage fits the supplied universe. -/
theorem MeasuredEliminationWalk :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ∃ run : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) run ∧
      ∀ (φ U : CNF) (order : List ℕ),
        let result := run (pair (encodeClause (order.map (fun x => (x,true))))
          (pair (encodeCNF φ) (encodeCNF U)))
        (result ≠ [] ↔ ∀ j ≤ order.length, (order.take j).foldl eliminate (clauses φ) ⊆ clauses U) ∧
        (result ≠ [] → ∃ ψ : CNF, result = true :: encodeCNF ψ ∧
          clauses ψ = order.foldl eliminate (clauses φ)) := by
  dsimp only
  obtain ⟨elim,he,hes⟩ := MeasuredDavisPutnamStep
  obtain ⟨intersect,hi,his⟩ := MeasuredCNFIntersection
  obtain ⟨test,ht,hts⟩ := MeasuredCNFSubset
  let getOrder := fun s : Raw => (unpairB s).1
  let getRoot := fun s : Raw => (unpairB (unpairB s).2).1
  let getU := fun s : Raw => (unpairB (unpairB s).2).2
  let init := fun s : Raw => pack (getU s) (getOrder s) (getRoot s)
    (bflag (test (getRoot s,getU s)))
  let iter := fun s : Raw => (step elim intersect test)^[(getOrder s).length] (init s)
  let run := fun s : Raw => sel (valid (iter s)) [] (true :: current (iter s))
  have ho := cpt_unpairB1
  have hf := cpt_unpairB1_1 cpt_unpairB2
  have hu := cpt_unpairB2_1 cpt_unpairB2
  have hflag := cpt_bitFlag (cpt_comp (cpt_pair hf hu) ht)
  have hinit : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) init :=
    cpt_pairB2 hu (cpt_pairB2 ho (cpt_pairB2 hf hflag))
  have hr : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) iter :=
    cpt_iterMeasure (step_cpt he hi ht) allowance 4 (step_allowance _ _ _) (step_length _ _ _)
      allowance_bound ho hinit
  have rest := cpt_unpairB2_1 (cpt_unpairB2_1 hr)
  have hrun : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) run :=
    cpt_sel (cpt_unpairB2_1 rest) (cpt_const []) (cpt_app2 (cpt_const [true]) (cpt_unpairB1_1 rest))
  refine ⟨run,hrun,fun φ U order => ?_⟩
  change (run (pairB (orderCode order) (pairB (encodeCNF φ) (encodeCNF U))) ≠ [] ↔ _) ∧ _
  have hlen : order.length ≤ (orderCode order).length := by
    induction order with
    | nil => simp
    | cons x xs ih =>
      have h : orderCode (x::xs) = encodeLiteral (x,true) ++ orderCode xs := by simp [orderCode,encodeClause]
      rw [List.length_cons,h,List.length_append]
      have hb : 1 ≤ (encodeLiteral (x,true)).length := by simp [encodeLiteral]
      omega
  let result := (step elim intersect test)^[(orderCode order).length]
    (pack (encodeCNF U) (orderCode order) (encodeCNF φ) (bflag (test (encodeCNF φ,encodeCNF U))))
  have hs := walk_spec elim intersect test hes his hts U φ order _ hlen _ (hts φ U)
  have hinitShape : valid (pack (encodeCNF U) (orderCode order) (encodeCNF φ)
      (bflag (test (encodeCNF φ,encodeCNF U)))) = [] ∨
      valid (pack (encodeCNF U) (orderCode order) (encodeCNF φ)
        (bflag (test (encodeCNF φ,encodeCNF U)))) = [true] := by
    rw [(projections _ _ _ _).2.2.2]
    exact flag_shape _
  have hshape : valid result = [] ∨ valid result = [true] := iterate_shape elim intersect test _ _ hinitShape
  have hresult : run (pairB (orderCode order) (pairB (encodeCNF φ) (encodeCNF U))) =
      sel (valid result) [] (true :: current result) := by
    simp only [run,iter,init,getOrder,getU,getRoot,unpairB_pairB,result]
  let stages : Prop := ∀ j ≤ order.length,
    (order.take j).foldl (fun G x => eliminateVariable x G) (clauseSet φ) ⊆ clauseSet U
  let final := order.foldl (fun G x => eliminateVariable x G) (clauseSet φ)
  let spec := fun w : Raw => (w ≠ [] ↔ stages) ∧
    (w ≠ [] → ∃ ψ : CNF, w = true :: encodeCNF ψ ∧ clauseSet ψ = final)
  let word := sel (valid result) [] (true :: current result)
  have heq : word ≠ [] ↔ valid result = [true] := by
    dsimp only [word]
    rcases hshape with h | h
    · rw [h]
      simp [sel]
    · rw [h]
      simp [sel]
  have hspec : spec word := by
    change (word ≠ [] ↔ stages) ∧ _
    refine ⟨heq.trans (hs.1.trans (covered_iff _ _ _)),fun hp => ?_⟩
    have hv := heq.mp hp
    obtain ⟨ψ,hψ,hset⟩ := hs.2 hv
    refine ⟨ψ,?_,hset⟩
    change sel (valid result) [] (true :: current result) = true :: encodeCNF ψ
    rw [hv,hψ]
    rfl
  change spec (run (pairB (orderCode order) (pairB (encodeCNF φ) (encodeCNF U))))
  exact Eq.mpr (congrArg spec hresult) hspec

end PEqualNP.Outside
