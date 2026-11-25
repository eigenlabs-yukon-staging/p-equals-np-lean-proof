import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

private def state (x r n : Raw) := pairB x (pairB r n)
private def key (s : Raw) := (unpairB s).1
private def remaining (s : Raw) := (unpairB (unpairB s).2).1
private def count (s : Raw) := (unpairB (unpairB s).2).2

private theorem projection (x r n : Raw) :
    key (state x r n) = x ∧ remaining (state x r n) = r ∧ count (state x r n) = n := by
  simp [state,key,remaining,count,unpairB_pairB]

private def firstVar (r : Raw) := (headI r).tail.tail

private def next (s : Raw) : Raw :=
  sel (hd (remaining s)) s
    (sel (bflag (decide (key s = firstVar (remaining s))))
      (state (key s) (dropI (remaining s)) (true :: count s)) s)

private theorem next_cpt : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) next := by
  have hk := cpt_unpairB1
  have hr := cpt_unpairB1_1 cpt_unpairB2
  have hc := cpt_unpairB2_1 cpt_unpairB2
  have hf := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  exact cpt_sel (cpt_comp hr cpt_hd) cpt_id
    (cpt_sel (cpt_eqF hk hf) (cpt_pairB2 hk (cpt_pairB2 (cpt_comp hr cpt_dropI) (cpt_cons1 true hc))) cpt_id)

private theorem next_length (s : Raw) : (next s).length ≤ s.length + 3 := by
  unfold next sel
  split
  · omega
  · split
    · have h1 := unpairB_length s
      have h2 := unpairB_length (unpairB s).2
      have h3 := dropI_length (remaining s)
      simp only [state,pairB_length,List.length_cons]
      dsimp only [key,remaining,count] at h3 ⊢
      omega
    · omega

private theorem clause_cons (l : Literal) (c : Clause) : encodeClause (l::c) = encodeLiteral l ++ encodeClause c := by
  simp [encodeClause]

private theorem done (x n : Raw) : next (state x (encodeClause []) n) = state x (encodeClause []) n := by
  simp only [next,(projection _ _ _).2.1,show hd (encodeClause []) = [] by rfl,sel,ite_true]

private theorem next_cons (x : ℕ) (l : Literal) (c : Clause) (n : Raw) :
    next (state (vcode x) (encodeClause (l::c)) n) =
      if x = l.1 then state (vcode x) (encodeClause (l::c)) n
      else state (vcode x) (encodeClause c) (true::n) := by
  have hhead : hd (encodeClause (l::c)) ≠ [] := by rw [clause_cons]; simp [hd,encodeLiteral_eq]
  have hv : firstVar (encodeClause (l::c)) = vcode l.1 := by
    rw [firstVar,clause_cons,headI_lit,encodeLiteral_eq]
    rfl
  simp only [next,(projection _ _ _).1,(projection _ _ _).2.1,(projection _ _ _).2.2,sel,hhead,ite_false,hv]
  have hdrop : dropI (encodeClause (l::c)) = encodeClause c := by rw [clause_cons,dropI_lit]
  rw [hdrop]
  by_cases h : x = l.1
  · simp [h,bflag]
  · have hn : vcode x ≠ vcode l.1 := fun h' => h (vcode_injective h')
    simp [h,hn,bflag]

private theorem frozen {s : Raw} (h : next s = s) (n : ℕ) : next^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,h,ih]

private theorem iter_spec (x : ℕ) (c : Clause) (n : ℕ) (h : c.length ≤ n) (acc : Raw) :
    count (next^[n] (state (vcode x) (encodeClause c) acc)) =
      List.replicate ((c.map Prod.fst).idxOf x) true ++ acc := by
  induction c generalizing n acc with
  | nil =>
    rw [frozen (done _ _) n,(projection _ _ _).2.2]
    rfl
  | cons l c ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      by_cases he : x = l.1
      · have hfix : next (state (vcode x) (encodeClause (l::c)) acc) = state (vcode x) (encodeClause (l::c)) acc := by
          simp [next_cons,he]
        rw [frozen hfix,(projection _ _ _).2.2]
        simp [he]
      · rw [Function.iterate_succ_apply,next_cons,if_neg he,ih n (by simpa using h)]
        have he' : l.1 ≠ x := Ne.symm he
        simp only [List.map_cons,List.idxOf_cons,beq_eq_false_iff_ne.mpr he',Bool.false_eq_true,
          ite_false,List.replicate_succ',List.append_assoc,List.singleton_append]

/-- Count the literals before the first occurrence of a variable, returning
the entire literal count when the variable does not occur. -/
theorem MeasuredFirstOccurrenceIndex :
    ∃ index : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) index ∧
      ∀ (l : Literal) (c : Clause), index (encodeLiteral l,encodeClause c) =
        List.replicate ((c.map Prod.fst).idxOf l.1) true := by
  let init := fun s : Raw => state (unpairB s).1.tail.tail (unpairB s).2 []
  let run := fun s : Raw => count (next^[(unpairB s).2.length] (init s))
  have hi : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) init :=
    cpt_pairB2 (cpt_tail1 (cpt_tail1 cpt_unpairB1)) (cpt_pairB2 cpt_unpairB2 (cpt_const []))
  have hv := cpt_iterGrow next_cpt 3 next_length cpt_unpairB2 hi
  have hr : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) run :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hv)
  refine ⟨fun p => run (pairB p.1 p.2),cpt_comp (g := run) cpt_pairB hr,fun l c => ?_⟩
  have hlen : c.length ≤ (encodeClause c).length := by
    induction c with
    | nil => simp
    | cons l c ih =>
      rw [List.length_cons,clause_cons,List.length_append]
      have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega
  have hx : (encodeLiteral l).tail.tail = vcode l.1 := by simp [encodeLiteral_eq]
  simp only [run,init,unpairB_pairB,hx,iter_spec l.1 c _ hlen,List.append_nil]

end PEqualNP.Outside
