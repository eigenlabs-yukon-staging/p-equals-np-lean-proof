import PEqualNP.Library.SearchHelpers.SearchToDecision
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def unitRaw (b : Bool) (word : List Bool) : List Bool :=
  true :: b :: (word ++ [false,false])

private def units (ls : List Literal) : CNF := ls.map (fun l => [l])

private def trueVars (ls : List Literal) : List ℕ := (ls.filter (fun l => l.2)).map Prod.fst

private def witnessCode (ls : List Literal) : List Bool := (trueVars ls).flatMap vcode

private def itemCode (o : Option Literal) : List Bool :=
  o.elim [false,false] encodeLiteral

private def items (φ : CNF) : List (Option Literal) :=
  φ.flatMap (fun c => c.map some ++ [none])

private theorem encode_items (φ : CNF) : (items φ).flatMap itemCode = encodeCNF φ := by
  simp only [items,encodeCNF,List.flatMap_assoc,List.flatMap_append,List.flatMap_map,itemCode]
  apply List.flatMap_congr
  intro c _
  simp [encodeClause,itemCode]

private theorem items_size (xs : List (Option Literal)) :
    xs.length ≤ (xs.flatMap itemCode).length := by
  induction xs with
  | nil => rfl
  | cons o xs ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      have h : 1 ≤ (itemCode o).length := by cases o <;> simp [itemCode,encodeLiteral]
      omega

private theorem mem_items (φ : CNF) (c : Clause) (l : Literal) (hc : c ∈ φ) (hl : l ∈ c) :
    some l ∈ items φ := by
  exact List.mem_flatMap.mpr ⟨c,hc,List.mem_append_left _ (List.mem_map_of_mem hl)⟩

private theorem vcode_length_le_literal (l : Literal) : (vcode l.1).length ≤ (encodeLiteral l).length := by
  simp [encodeLiteral_eq]
  omega

private theorem encode_cat (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF,List.flatMap_append]

private theorem units_snoc (ls : List Literal) (l : Literal) :
    units (ls ++ [l]) = units ls ++ [[l]] := by simp [units]

private theorem unit_raw (i : ℕ) (b : Bool) : unitRaw b (vcode i) = encodeClause [(i,b)] := by
  simp [unitRaw,encodeClause,encodeLiteral_eq]

private theorem witness_snoc (ls : List Literal) (l : Literal) :
    witnessCode (ls ++ [l]) = witnessCode ls ++ (if l.2 then vcode l.1 else []) := by
  cases l with
  | mk i b => cases b <;> simp [witnessCode,trueVars,List.filter_append,List.flatMap_append]

private def step (query : List Bool → List Bool) (s : List Bool) : List Bool :=
  let original := (unpairB s).1
  let remaining := (unpairB (unpairB s).2).1
  let selected := (unpairB (unpairB (unpairB s).2).2).1
  let witness := (unpairB (unpairB (unpairB s).2).2).2
  let word := headI remaining
  let v := tk original word.tail.tail
  let check := query (original ++ (selected ++ unitRaw true v))
  if remaining = [] then s
  else if word.headD false then pairB original (pairB (dropI remaining)
    (pairB (selected ++ sel check (unitRaw false v) (unitRaw true v)) (witness ++ sel check [] v)))
  else pairB original (pairB (dropI remaining) (pairB selected witness))

private theorem step_cpt {query : List Bool → List Bool}
    (hq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) query) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step query) := by
  have ho := cpt_unpairB1
  have hr := cpt_unpairB1_1 cpt_unpairB2
  have hh := cpt_unpairB2_1 cpt_unpairB2
  have hU := cpt_unpairB1_1 hh
  have hW := cpt_unpairB2_1 hh
  have hword := cpt_comp hr cpt_headI
  have hn := cpt_tk ho (cpt_tail1 (cpt_tail1 hword))
  have hunit (b : Bool) := cpt_cons1 true (cpt_cons1 b (cpt_app2 hn (cpt_const [false,false])))
  have hcheck := cpt_comp (cpt_app2 ho (cpt_app2 hU (hunit true))) hq
  have hyes := cpt_pairB2 (cpt_app2 hU (cpt_sel hcheck (hunit false) (hunit true)))
    (cpt_app2 hW (cpt_sel hcheck (cpt_const []) hn))
  have hno := cpt_pairB2 hU hW
  have hnext := cpt_pairB2 ho (cpt_pairB2 (cpt_comp hr cpt_dropI)
    (cpt_sel (cpt_hd1 hword) hno hyes))
  refine cptE (cpt_sel hr cpt_id hnext) (fun s => ?_)
  dsimp only [step,sel,unitRaw]
  split
  · rfl
  · cases headI (unpairB (unpairB s).2).1 with
    | nil => rfl
    | cons b rest => cases b <;> rfl

private def measure (s : List Bool) : ℕ := 3*(unpairB s).1.length + 12

private theorem measure_preserved (query : List Bool → List Bool) (s : List Bool) :
    measure (step query s) ≤ measure s := by
  dsimp only [step]
  split
  · rfl
  · split <;> simp [measure,unpairB_pairB]

private theorem step_length (query : List Bool → List Bool) (s : List Bool) :
    (step query s).length ≤ s.length + measure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have ht := dropI_length (unpairB (unpairB s).2).1
  let v := tk (unpairB s).1 (headI (unpairB (unpairB s).2).1).tail.tail
  have hv : v.length ≤ (unpairB s).1.length := tk_length _ _
  dsimp only [v] at hv
  dsimp only [step,measure]
  split
  · omega
  · split
    · simp only [pairB_length,List.length_append,unitRaw,sel]
      by_cases hcheck : query ((unpairB s).1 ++ ((unpairB (unpairB (unpairB s).2).2).1 ++
        true :: true :: (tk (unpairB s).1 (headI (unpairB (unpairB s).2).1).tail.tail ++ [false,false]))) = [] <;>
        simp only [hcheck,ite_true,ite_false,List.length_append,List.length_cons,List.length_nil] <;> omega
    · simp only [pairB_length]
      omega

private theorem measure_bound (s : List Bool) : measure s ≤ 12*s.length+12 := by
  have h := unpairB_length s
  dsimp only [measure]
  omega

private theorem eval_app (σ : Assignment) (a b : CNF) :
    CNF.eval σ (a ++ b) = true ↔ CNF.eval σ a = true ∧ CNF.eval σ b = true := by
  simp [CNF.eval,List.all_append]

private theorem eval_unit (σ : Assignment) (i : ℕ) (b : Bool) :
    CNF.eval σ [[(i,b)]] = true ↔ σ i = b := by
  simp [CNF.eval,Clause.eval,Literal.eval]

private theorem unit_constraints (σ : Assignment) (ls : List Literal)
    (h : CNF.eval σ (units ls) = true) : ∀ l ∈ ls, σ l.1 = l.2 := by
  intro l hl
  have hh := List.all_eq_true.mp h [l] (List.mem_map.mpr ⟨l,hl,rfl⟩)
  simpa [Clause.eval,Literal.eval] using hh

private theorem clip_literal (orig : List Bool) (l : Literal)
    (h : (encodeLiteral l).length ≤ orig.length) :
    tk orig (encodeLiteral l).tail.tail = vcode l.1 := by
  have hv := vcode_length_le_literal l
  rw [tk_eq,encodeLiteral_eq]
  exact List.take_of_length_le (hv.trans h)

private theorem item_nonempty (o : Option Literal) (xs : List Bool) : itemCode o ++ xs ≠ [] := by
  cases o <;> simp [itemCode,encodeLiteral]

private theorem search_run (d : List Bool → Bool) (φ : CNF)
    (hspec : ∀ ls : List Literal, d (encodeCNF (φ ++ units ls)) = true ↔ Satisfiable (φ ++ units ls))
    (xs : List (Option Literal)) (ls : List Literal) (n : ℕ)
    (hn : xs.length ≤ n)
    (hc : ∀ o ∈ xs, (itemCode o).length ≤ (encodeCNF φ).length)
    (hSat : Satisfiable (φ ++ units ls)) :
    ∃ ls' : List Literal,
      Satisfiable (φ ++ units ls') ∧
      (∀ l ∈ ls, l ∈ ls') ∧
      (∀ l : Literal, some l ∈ xs → ∃ t ∈ ls', t.1 = l.1) ∧
      (witnessCode ls').length ≤ (witnessCode ls).length + (xs.flatMap itemCode).length ∧
      (step (fun a => if d a then [true] else []))^[n]
        (pairB (encodeCNF φ) (pairB (xs.flatMap itemCode)
          (pairB (encodeCNF (units ls)) (witnessCode ls)))) =
        pairB (encodeCNF φ) (pairB [] (pairB (encodeCNF (units ls')) (witnessCode ls'))) := by
  induction n generalizing xs ls with
  | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      exact ⟨ls,hSat,fun _ h => h,by simp,by simp,rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases xs with
      | nil =>
          have e : step (fun a => if d a then [true] else [])
              (pairB (encodeCNF φ) (pairB ([] : List Bool)
                (pairB (encodeCNF (units ls)) (witnessCode ls)))) =
              pairB (encodeCNF φ) (pairB [] (pairB (encodeCNF (units ls)) (witnessCode ls))) := by
            simp [step,unpairB_pairB]
          simp only [List.flatMap_nil]
          rw [e]
          simpa using ih [] ls (by simp) (by simp) hSat
      | cons o xs =>
          have hn' : xs.length ≤ n := by simpa using hn
          have hc' : ∀ o ∈ xs, (itemCode o).length ≤ (encodeCNF φ).length :=
            fun a ha => hc a (List.mem_cons_of_mem _ ha)
          have hl := hc o List.mem_cons_self
          have he := item_nonempty o (xs.flatMap itemCode)
          cases o with
          | none =>
              have e : step (fun a => if d a then [true] else [])
                    (pairB (encodeCNF φ) (pairB ((none :: xs).flatMap itemCode)
                      (pairB (encodeCNF (units ls)) (witnessCode ls)))) =
                  pairB (encodeCNF φ) (pairB (xs.flatMap itemCode)
                    (pairB (encodeCNF (units ls)) (witnessCode ls))) := by
                simp [step,unpairB_pairB,itemCode,headI,dropI]
              rw [e]
              obtain ⟨ls',ha,hb,hg,hd,hr⟩ := ih xs ls hn' hc' hSat
              exact ⟨ls',ha,hb,fun l hl => hg l (by simpa using hl),
                by simpa only [List.flatMap_cons,List.length_append] using
                  hd.trans (Nat.add_le_add_left (Nat.le_add_left _ _) _),hr⟩
          | some l =>
              let test := encodeCNF (φ ++ units (ls ++ [(l.1,true)]))
              let b := d test
              let next := ls ++ [(l.1,b)]
              have hnext : Satisfiable (φ ++ units next) := by
                change Satisfiable (φ ++ units (ls ++ [(l.1,b)]))
                cases hb : d test with
                | true =>
                    have hb' : b = true := hb
                    rw [hb']
                    exact (hspec _).mp hb
                | false =>
                    have hb' : b = false := hb
                    rw [hb']
                    obtain ⟨σ,hσ⟩ := hSat
                    have hσb : σ l.1 = false := by
                      cases hσ' : σ l.1 with
                      | false => rfl
                      | true =>
                          have hh : Satisfiable (φ ++ units (ls ++ [(l.1,true)])) := by
                            refine ⟨σ,?_⟩
                            rw [units_snoc,← List.append_assoc,eval_app]
                            exact ⟨hσ,(eval_unit _ _ _).mpr hσ'⟩
                          have ht := (hspec _).mpr hh
                          rw [hb] at ht
                          simp at ht
                    refine ⟨σ,?_⟩
                    rw [units_snoc,← List.append_assoc,eval_app]
                    exact ⟨hσ,(eval_unit _ _ _).mpr hσb⟩
              have hq : encodeCNF φ ++ (encodeCNF (units ls) ++ unitRaw true (vcode l.1)) = test := by
                have heq : encodeClause [(l.1,true)] = encodeCNF [[(l.1,true)]] := by simp [encodeCNF]
                rw [unit_raw,heq,← encode_cat,← encode_cat,← units_snoc]
              have hbranch : step (fun a => if d a then [true] else [])
                  (pairB (encodeCNF φ) (pairB ((some l :: xs).flatMap itemCode)
                    (pairB (encodeCNF (units ls)) (witnessCode ls)))) =
                pairB (encodeCNF φ) (pairB (xs.flatMap itemCode)
                  (pairB (encodeCNF (units next)) (witnessCode next))) := by
                have hx : (some l :: xs).flatMap itemCode = encodeLiteral l ++ xs.flatMap itemCode := rfl
                rw [hx]
                have hne : encodeLiteral l ++ xs.flatMap itemCode ≠ [] := he
                simp only [step,unpairB_pairB,ite_eq_right hne,headI_lit,dropI_lit,
                  clip_literal _ l hl,hq]
                have hhead : (encodeLiteral l).headD false = true := rfl
                rw [hhead]
                simp only [ite_true, next, units_snoc, encode_cat, witness_snoc]
                cases hb : d test <;> simp [b,hb,sel,unit_raw,encodeCNF]
              rw [hbranch]
              obtain ⟨ls',ha,hb,hg,hd,hr⟩ := ih xs next hn' hc' hnext
              have hlen : (witnessCode next).length ≤ (witnessCode ls).length + (encodeLiteral l).length := by
                have hv := vcode_length_le_literal l
                simp only [next,witness_snoc,List.length_append]
                split <;> simp_all
              refine ⟨ls',ha,fun a hm => hb a (List.mem_append_left _ hm),?_,?_,hr⟩
              · intro t ht
                simp only [List.mem_cons,Option.some.injEq] at ht
                rcases ht with heq | ht
                · have hidx : l.1 = t.1 := congrArg (fun a : Literal => a.1) heq.symm
                  exact ⟨(l.1,b),hb _ (List.mem_append_right _ (by simp)),hidx⟩
                · exact hg t ht
              · simp only [List.flatMap_cons,itemCode,Option.elim_some,List.length_append]
                omega

/-- A measured SAT search uses only variable codes present in the formula.
It needs a decider only for the formula with arbitrary unit constraints appended. -/
theorem SparseVariableSATSearch (D : Language Bool) (hD : D ∈ P) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∀ ls : List Literal,
          encodeCNF (φ ++ ls.map (fun l => [l])) ∈ D ↔ Satisfiable (φ ++ ls.map (fun l => [l]))) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  obtain ⟨d,hd,hcd⟩ := hD
  let query := fun a => if d a then [true] else []
  let initial := fun a => pairB a (pairB a (pairB [] []))
  let search := fun a => (unpairB (unpairB (unpairB ((step query)^[a.length] (initial a))).2).2).2
  have hi := cpt_pairB2 cpt_id (cpt_pairB2 cpt_id (cpt_const (pairB [] [])))
  have hl := cpt_iterMeasure (step_cpt (cpt_bitFlag hcd)) measure 12
    (measure_preserved query) (step_length query) measure_bound cpt_id hi
  have hsearch : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hl))
  refine ⟨search,hsearch,fun φ hspec hSat => ?_⟩
  have hspec' (ls : List Literal) : d (encodeCNF (φ ++ units ls)) = true ↔ Satisfiable (φ ++ units ls) :=
    (hd _).symm.trans (hspec ls)
  have hsize : (items φ).length ≤ (encodeCNF φ).length := by rw [← encode_items]; exact items_size _
  have hlenItems (xs : List (Option Literal)) (o : Option Literal) (ho : o ∈ xs) :
      (itemCode o).length ≤ (xs.flatMap itemCode).length := by
    induction xs with
    | nil => simp at ho
    | cons a as ih =>
        simp only [List.mem_cons] at ho
        simp only [List.flatMap_cons,List.length_append]
        rcases ho with rfl | ho
        · omega
        · have := ih ho
          omega
  have hc : ∀ o ∈ items φ, (itemCode o).length ≤ (encodeCNF φ).length := by
    intro o ho
    rw [← encode_items]
    exact hlenItems _ _ ho
  obtain ⟨ls,⟨σ,hsat⟩,_,hcoverage,hlen,hstate⟩ :=
    search_run d φ hspec' (items φ) [] (encodeCNF φ).length hsize hc (by simpa [units])
  have hnil : encodeCNF (units []) = [] := rfl
  have hwNil : witnessCode [] = [] := rfl
  simp only [encode_items,hnil,hwNil] at hstate
  have hout : search (encodeCNF φ) = witnessCode ls := by
    dsimp only [search,initial,query]
    rw [hstate]
    simp only [unpairB_pairB]
  refine ⟨trueVars ls, ?_, ?_, ?_⟩
  · rw [hout]
    rfl
  · rw [hout]
    simpa [witnessCode,trueVars,encode_items] using hlen
  · obtain ⟨hφ,hu⟩ := (eval_app _ _ _).mp hsat
    have hσ := unit_constraints σ ls hu
    have hvalue (l : Literal) (h : some l ∈ items φ) : decide (l.1 ∈ trueVars ls) = σ l.1 := by
      obtain ⟨a,ha,he⟩ := hcoverage l h
      cases hv : σ l.1 with
      | true =>
          have hac := hσ a ha
          rw [he,hv] at hac
          have hm : l.1 ∈ trueVars ls := by
            exact List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨ha,hac.symm⟩,he⟩
          simp [hm]
      | false =>
          have hm : l.1 ∉ trueVars ls := by
            intro hm
            obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
            obtain ⟨ha,ht⟩ := List.mem_filter.mp ha
            have hh := hσ a ha
            change a.1 = l.1 at he
            rw [he,hv,ht] at hh
            contradiction
          simp [hm]
    simp only [CNF.eval,List.all_eq_true,Clause.eval,List.any_eq_true,Literal.eval] at hφ ⊢
    intro c hc
    obtain ⟨l,hl,ht⟩ := hφ c hc
    exact ⟨l,hl,by rw [hvalue l (mem_items φ c l hc hl)]; exact ht⟩

end PEqualNP.Outside
