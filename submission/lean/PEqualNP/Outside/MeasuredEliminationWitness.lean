import PEqualNP.Outside.MeasuredEliminationWalk
import PEqualNP.Outside.MeasuredReverseClause
import PEqualNP.Outside.EliminationAssignmentLift
import PEqualNP.Outside.FullEliminationSAT
import PEqualNP.Library.SearchHelpers.SatVerifierCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search
open PEqualNP.ProofComplexity (Satisfies)

private abbrev Raw := List Bool
private def code (order : List ℕ) : Raw := encodeClause (order.map (fun x => (x,true)))
private def stage (φ : CNF) (order : List ℕ) : Set NatClause :=
  order.foldl (fun G x => eliminateVariable x G) (clauseSet φ)
private def covers (φ U : CNF) (order : List ℕ) : Prop :=
  ∀ j ≤ order.length, stage φ (order.take j) ⊆ clauseSet U

private def state (r φ U w : Raw) := pairB r (pairB φ (pairB U w))
private def rem (s : Raw) := (unpairB s).1
private def root (s : Raw) := (unpairB (unpairB s).2).1
private def ambient (s : Raw) := (unpairB (unpairB (unpairB s).2).2).1
private def wit (s : Raw) := (unpairB (unpairB (unpairB s).2).2).2

private theorem projection (r φ U w : Raw) :
    rem (state r φ U w) = r ∧ root (state r φ U w) = φ ∧ ambient (state r φ U w) = U ∧
      wit (state r φ U w) = w := by
  simp [state,rem,root,ambient,wit,unpairB_pairB]

private def pivot (s : Raw) := (headI (rem s)).tail.tail

private def advance (prior : Raw → Raw) (s : Raw) : Raw :=
  let w := sel (bflag (SV (prior s,wit s))) (pivot s ++ wit s) (wit s)
  state (dropI (rem s)) (root s) (ambient s) w

private def rewind (prior : Raw → Raw) (s : Raw) : Raw :=
  sel (hd (rem s)) s (advance prior s)

private theorem rewind_cpt {prior : Raw → Raw}
    (hp : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) prior) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (rewind prior) := by
  have hr := cpt_unpairB1
  have hf := cpt_unpairB1_1 cpt_unpairB2
  have htail := cpt_unpairB2_1 cpt_unpairB2
  have hU := cpt_unpairB1_1 htail
  have hw := cpt_unpairB2_1 htail
  have htest := cpt_bitFlag (cpt_comp (cpt_pair hp hw) cpt_SV)
  have hx := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  exact cpt_sel (cpt_comp hr cpt_hd) cpt_id
    (cpt_pairB2 (cpt_comp hr cpt_dropI) (cpt_pairB2 hf (cpt_pairB2 hU
      (cpt_sel htest (cpt_app2 hx hw) hw))))

private theorem advance_bound (prior : Raw → Raw) (s : Raw) :
    (advance prior s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hparts := congrArg List.length (headI_dropI (rem s))
  simp only [List.length_append] at hparts
  have hx : (pivot s).length ≤ (headI (rem s)).length := by
    unfold pivot
    simp only [List.length_tail]
    omega
  have hw : (sel (bflag (SV (prior s,wit s))) (pivot s ++ wit s) (wit s)).length ≤
      (pivot s).length + (wit s).length := by
    cases SV (prior s,wit s) <;> simp [sel,bflag]
  simp only [advance,state,pairB_length]
  dsimp only [rem,root,ambient,wit] at hparts hx hw ⊢
  omega

private theorem rewind_bound (prior : Raw → Raw) (s : Raw) :
    (rewind prior s).length ≤ s.length + 3 := by
  unfold rewind sel
  split
  · omega
  · exact advance_bound prior s

private theorem code_cons (x : ℕ) (xs : List ℕ) : code (x::xs) = encodeLiteral (x,true) ++ code xs := by
  simp [code,encodeClause]

private theorem rewind_done (prior : Raw → Raw) (φ U w : Raw) :
    rewind prior (state (code []) φ U w) = state (code []) φ U w := by
  simp only [rewind,(projection _ _ _ _).1,show hd (code []) = [] by rfl,sel,ite_true]

private theorem rewind_next (prior : Raw → Raw) (φ U ψ : CNF) (x : ℕ) (xs ys : List ℕ)
    (hprior : prior (state (code (x::xs)) (encodeCNF φ) (encodeCNF U) (ys.flatMap vcode)) =
      encodeCNF ψ) :
    let ys' := if SV (encodeCNF ψ,ys.flatMap vcode) then ys else x::ys
    rewind prior (state (code (x::xs)) (encodeCNF φ) (encodeCNF U) (ys.flatMap vcode)) =
      state (code xs) (encodeCNF φ) (encodeCNF U) (ys'.flatMap vcode) := by
  dsimp only
  have hd' : hd (code (x::xs)) ≠ [] := by
    rw [code_cons]
    simp [hd,encodeLiteral_eq]
  unfold rewind
  rw [(projection _ _ _ _).1]
  simp only [sel,hd',ite_false]
  have hpiv : pivot (state (code (x::xs)) (encodeCNF φ) (encodeCNF U) (ys.flatMap vcode)) = vcode x := by
    rw [pivot,(projection _ _ _ _).1,code_cons,headI_lit,encodeLiteral_eq]
    rfl
  simp only [advance,hprior,hpiv]
  simp only [(projection _ _ _ _).1,(projection _ _ _ _).2.1,(projection _ _ _ _).2.2.1,
    (projection _ _ _ _).2.2.2,code_cons,dropI_lit]
  cases SV (encodeCNF ψ,ys.flatMap vcode) <;>
    simp [sel,bflag]


private theorem covers_append_left (φ U : CNF) (xs ys : List ℕ) (h : covers φ U (xs ++ ys)) :
    covers φ U xs := by
  intro j hj
  have htake : (xs ++ ys).take j = xs.take j := List.take_append_of_le_length hj
  rw [← htake]
  exact h j (by simp only [List.length_append]; omega)

private theorem eliminated_absent (F : Set NatClause) (order : List ℕ) (x : ℕ) (hx : x ∈ order) :
    ∀ c ∈ order.foldl (fun G v => eliminateVariable v G) F, ∀ l ∈ c, l.1 ≠ x := by
  induction order generalizing F with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · clear ih
      let noX := fun G : Set NatClause => ∀ c ∈ G, ∀ l ∈ c, l.1 ≠ x
      have hs : ∀ (zs : List ℕ) G, noX G → noX (zs.foldl (fun T v => eliminateVariable v T) G) := by
        intro zs
        induction zs with
        | nil => exact fun _ h => h
        | cons v zs ih =>
          intro G h
          apply ih (eliminateVariable v G)
          intro c hc l hl
          obtain ⟨_,d,hd,hld⟩ := eliminate_support hc l hl
          exact h d hd l hld
      exact hs ys _ (fun c hc l hl => (eliminate_support hc l hl).1)
    · exact ih (eliminateVariable y F) hx

private theorem elimination_absent_identity (F : Set NatClause) (x : ℕ)
    (hx : ∀ c ∈ F, ∀ l ∈ c, l.1 ≠ x) : eliminateVariable x F = F := by
  ext c
  constructor
  · rintro (⟨hc,_,_⟩ | ⟨p,hp,n,hn,hpos,_,_,_,_⟩)
    · exact hc
    · exact (hx p hp (x,true) hpos rfl).elim
  · intro hc
    exact Or.inl ⟨hc,fun h => hx c hc (x,true) h rfl,fun h => hx c hc (x,false) h rfl⟩

private theorem rewind_spec (prior : Raw → Raw) (φ U : CNF)
    (hprior : ∀ x xs w, covers φ U xs.reverse →
      ∃ ψ : CNF, prior (state (code (x::xs)) (encodeCNF φ) (encodeCNF U) w) = encodeCNF ψ ∧
      clauseSet ψ = stage φ xs.reverse)
    (xs ys : List ℕ) (n : ℕ) (hlen : xs.length ≤ n)
    (hcover : covers φ U xs.reverse)
    (hdisjoint : ∀ v ∈ xs, v ∉ ys)
    (hmodel : Satisfies (asg (ys.flatMap vcode)) (stage φ xs.reverse)) :
    ∃ vs : List ℕ, wit ((rewind prior)^[n] (state (code xs) (encodeCNF φ) (encodeCNF U) (ys.flatMap vcode))) =
      vs.flatMap vcode ∧ Satisfies (asg (vs.flatMap vcode)) (clauseSet φ) := by
  induction xs generalizing ys n with
  | nil =>
    clear hlen hcover hdisjoint
    refine ⟨ys,?_,hmodel⟩
    induction n with
    | zero => exact (projection _ _ _ _).2.2.2
    | succ n ih => rw [Function.iterate_succ_apply,rewind_done,ih]
  | cons x xs ih =>
    cases n with
    | zero => simp at hlen
    | succ n =>
      have hc : covers φ U xs.reverse := covers_append_left φ U _ [_] (by simpa [List.reverse_cons] using hcover)
      obtain ⟨ψ,hψ,hset⟩ := hprior x xs (ys.flatMap vcode) hc
      rw [Function.iterate_succ_apply,rewind_next prior φ U ψ x xs ys hψ]
      let next := if SV (encodeCNF ψ,ys.flatMap vcode) then ys else x::ys
      have hstage : stage φ (x::xs).reverse = eliminateVariable x (clauseSet ψ) := by
        rw [hset]
        simp [stage,List.reverse_cons,List.foldl_append]
      have hsat : Satisfies (asg (next.flatMap vcode)) (stage φ xs.reverse) := by
        rw [← hset]
        exact lift_codes ψ x ys (hdisjoint x List.mem_cons_self) (hstage ▸ hmodel)
      have hnext : ∀ v ∈ xs, v ∉ next := by
        intro v hv
        have hv' := hdisjoint v (List.mem_cons_of_mem x hv)
        by_cases he : v = x
        · have hx : x ∈ xs.reverse := by simpa [he] using hv
          have hId := elimination_absent_identity (stage φ xs.reverse) x
            (eliminated_absent (clauseSet φ) xs.reverse x hx)
          have hEq : stage φ (x::xs).reverse = clauseSet ψ := by
            rw [hstage,hset,hId]
          have hSat : Satisfies (asg (ys.flatMap vcode)) (clauseSet ψ) := hEq ▸ hmodel
          have hSV := (sv_satisfies_iff ψ _).mpr hSat
          simpa [next,hSV] using hv'
        · unfold next
          split <;> simp [he,hv']
      exact ih next n (by simpa using hlen) hc hnext hsat

private theorem code_bound (xs : List ℕ) : xs.length ≤ (code xs).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons,code_cons,List.length_append]
    have h : 1 ≤ (encodeLiteral (x,true)).length := by simp [encodeLiteral]
    omega

private theorem reverse_order (reverse : Raw → Raw)
    (hr : ∀ c : Clause, reverse (encodeClause c) = encodeClause c.reverse) (xs : List ℕ) :
    reverse (code xs) = code xs.reverse := by
  simp only [code,hr,List.map_reverse]


private def searchWord (walk reverse : Raw → Raw) (s : Raw) : Raw :=
  (walk (pairB (reverse (dropI (rem s))) (pairB (root s) (ambient s)))).tail

private theorem searchWord_cpt {walk reverse : Raw → Raw}
    (hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) walk)
    (hr : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) reverse) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (searchWord walk reverse) := by
  have hrem := cpt_unpairB1
  have hroot := cpt_unpairB1_1 cpt_unpairB2
  have hU := cpt_unpairB1_1 (cpt_unpairB2_1 cpt_unpairB2)
  have hrev := cpt_comp (cpt_comp hrem cpt_dropI) hr
  exact cpt_tail1 (cpt_comp (cpt_pairB2 hrev (cpt_pairB2 hroot hU)) hw)

private theorem searchWord_spec (walk reverse : Raw → Raw)
    (hRev : ∀ c : Clause, reverse (encodeClause c) = encodeClause c.reverse)
    (hwalk : ∀ (φ U : CNF) (order : List ℕ), covers φ U order →
      ∃ ψ : CNF, walk (pairB (code order) (pairB (encodeCNF φ) (encodeCNF U))) =
        true :: encodeCNF ψ ∧ clauseSet ψ = stage φ order)
    (φ U : CNF) (x : ℕ) (xs : List ℕ) (w : Raw) (hc : covers φ U xs.reverse) :
    ∃ ψ : CNF, searchWord walk reverse (state (code (x::xs)) (encodeCNF φ) (encodeCNF U) w) =
      encodeCNF ψ ∧ clauseSet ψ = stage φ xs.reverse := by
  obtain ⟨ψ,hw,hψ⟩ := hwalk φ U xs.reverse hc
  refine ⟨ψ,?_,hψ⟩
  simp only [searchWord,(projection _ _ _ _).1,(projection _ _ _ _).2.1,
    (projection _ _ _ _).2.2.1,code_cons,dropI_lit,reverse_order reverse hRev xs,hw,List.tail_cons]

set_option maxHeartbeats 600000 in
/-- Recover a sparse satisfying assignment in polynomial time by replaying
covered, complete variable elimination in reverse order. -/
theorem MeasuredEliminationWitness :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    let varCode := fun i : ℕ => (i.bits.flatMap fun b => [true,b]) ++ [false,true]
    let clauses := fun (φ : CNF) =>
      {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
    let eliminate := fun (G : Set (PEqualNP.ProofComplexity.Clause ℕ)) (x : ℕ) =>
      {C | (C ∈ G ∧ (x,true) ∉ C ∧ (x,false) ∉ C) ∨
        ∃ P ∈ G, ∃ N ∈ G, (x,true) ∈ P ∧ (x,false) ∉ P ∧
          (x,false) ∈ N ∧ (x,true) ∉ N ∧ C = P.erase (x,true) ∪ N.erase (x,false)}
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ (φ U : CNF) (order : List ℕ),
        (∀ c ∈ clauses φ, ∀ l ∈ c, l.1 ∈ order) →
        (∀ j ≤ order.length, (order.take j).foldl eliminate (clauses φ) ⊆ clauses U) →
        let result := search (pair (encodeClause (order.map (fun x => (x,true))))
          (pair (encodeCNF φ) (encodeCNF U)))
        (result = [] ↔ ¬ Satisfiable φ) ∧
        (Satisfiable φ → ∃ vs : List ℕ, result = true :: vs.flatMap varCode ∧
          CNF.eval (fun x => decide (x ∈ vs)) φ = true) := by
  dsimp only
  obtain ⟨walk,hw,hws⟩ := MeasuredEliminationWalk
  obtain ⟨reverse,hrev,hrspec⟩ := MeasuredReverseClause
  let prior := searchWord walk reverse
  let getOrder := fun s : Raw => (unpairB s).1
  let getRoot := fun s : Raw => (unpairB (unpairB s).2).1
  let getU := fun s : Raw => (unpairB (unpairB s).2).2
  let init := fun s : Raw => state (reverse (getOrder s)) (getRoot s) (getU s) []
  let iter := fun s : Raw => (rewind prior)^[(getOrder s).length] (init s)
  let candidate := fun s : Raw => wit (iter s)
  let result := fun s : Raw => sel (bflag (SV (getRoot s,candidate s))) [] (true :: candidate s)
  have ho := cpt_unpairB1
  have hf := cpt_unpairB1_1 cpt_unpairB2
  have hu := cpt_unpairB2_1 cpt_unpairB2
  have hi : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) init :=
    cpt_pairB2 (cpt_comp ho hrev) (cpt_pairB2 hf (cpt_pairB2 hu (cpt_const [])))
  have hIter : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) iter :=
    cpt_iterGrow (rewind_cpt (searchWord_cpt hw hrev)) 3 (rewind_bound prior) ho hi
  have hCand : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) candidate :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hIter))
  have hResult : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) result :=
    cpt_sel (cpt_bitFlag (cpt_comp (cpt_pair hf hCand) cpt_SV)) (cpt_const []) (cpt_cons1 true hCand)
  have hWalk (φ U : CNF) (order : List ℕ) (hc : covers φ U order) :
      ∃ ψ : CNF, walk (pairB (code order) (pairB (encodeCNF φ) (encodeCNF U))) =
        true :: encodeCNF ψ ∧ clauseSet ψ = stage φ order :=
    (hws φ U order).2 ((hws φ U order).1.mpr hc)
  refine ⟨result,hResult,fun φ U order hsupp hcover => ?_⟩
  let s := pairB (code order) (pairB (encodeCNF φ) (encodeCNF U))
  have hroot : getRoot s = encodeCNF φ := by simp [s,getRoot,unpairB_pairB]
  have hCandidate : Satisfiable φ → ∃ vs : List ℕ, candidate s = vs.flatMap vcode ∧
      Satisfies (asg (vs.flatMap vcode)) (clauseSet φ) := by
    rintro ⟨a,ha⟩
    have hs : PEqualNP.ProofComplexity.Satisfiable (clauseSet φ) :=
      ⟨a,(cnf_satisfies_iff a φ).mp ha⟩
    have hf := (FullEliminationSAT (clauseSet φ) order hsupp).mp hs
    have hFinal : stage φ order = ∅ := hf
    have hback : stage φ order.reverse.reverse = ∅ := by simpa using hFinal
    have hmodel : Satisfies (asg (([] : List ℕ).flatMap vcode)) (stage φ order.reverse.reverse) := by
      rw [hback]
      exact fun d hd => hd.elim
    have hc : covers φ U order.reverse.reverse := by simpa using (show covers φ U order from hcover)
    have hlen : order.reverse.length ≤ (code order).length := by simpa using code_bound order
    have hdisj : ∀ v ∈ order.reverse, v ∉ ([] : List ℕ) := by simp
    have heq : candidate s = wit ((rewind prior)^[(code order).length]
        (state (code order.reverse) (encodeCNF φ) (encodeCNF U) ([] : Raw))) := by
      simp only [candidate,iter,init,s,getOrder,getRoot,getU,unpairB_pairB,reverse_order reverse hrspec order]
    rw [heq]
    exact rewind_spec prior φ U (searchWord_spec walk reverse hrspec hWalk φ U)
      order.reverse [] _ hlen hc hdisj hmodel
  change (result s = [] ↔ ¬ Satisfiable φ) ∧ _
  have hout : result s = sel (bflag (SV (encodeCNF φ,candidate s))) [] (true :: candidate s) := by
    simp only [result,hroot]
  have hpass (h : Satisfiable φ) : ∃ vs : List ℕ, result s = true :: vs.flatMap vcode ∧
      CNF.eval (fun x => decide (x ∈ vs)) φ = true := by
    obtain ⟨vs,hc,hs⟩ := hCandidate h
    have hok := (sv_satisfies_iff φ _).mpr hs
    have hag : (fun x => decide (x ∈ vs)) = asg (vs.flatMap vcode) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq,asg_codes]
    refine ⟨vs,?_,?_⟩
    · rw [hout,hc,hok]
      rfl
    · rw [hag]
      exact (cnf_satisfies_iff _ _).mpr hs
  refine ⟨⟨?_,?_⟩,hpass⟩
  · intro hzero h
    obtain ⟨vs,hcode,_⟩ := hpass h
    rw [hzero] at hcode
    cases hcode
  · intro hn
    rw [hout]
    have hf : SV (encodeCNF φ,candidate s) = false := Bool.eq_false_iff.mpr (fun hok =>
      hn ⟨asg (candidate s),(cnf_satisfies_iff _ _).mpr ((sv_satisfies_iff φ _).mp hok)⟩)
    rw [hf]
    rfl

end PEqualNP.Outside
