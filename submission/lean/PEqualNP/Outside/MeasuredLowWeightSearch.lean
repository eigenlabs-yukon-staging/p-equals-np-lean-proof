import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Outside.MeasuredClauseWeight
import PEqualNP.Outside.LowWeightProgress

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private def current (s : List Bool) := (unpairB (unpairB s).2).1
private def saved (s : List Bool) := (unpairB (unpairB s).2).2
private def budget (s : List Bool) := (unpairB s).1
private def state (cap cur acc : List Bool) := pairB cap (pairB cur acc)
private def key (c : List Bool) := (headI c).tail.tail
private def stateStep (pos neg : List Bool × List Bool → List Bool)
    (light : List Bool → Bool) (s : List Bool) : List Bool :=
  let x := current s
  let p := (key x, x)
  let b := light (pos p)
  let cap := budget s
  if x = [] then s else
    state cap (tk cap (if b then pos p else neg p))
      (tk cap (saved s ++ (if b then p.1 else [])))

private theorem current_state (cap cur acc : List Bool) :
    current (state cap cur acc) = cur := by simp [current,state,unpairB_pairB]
private theorem saved_state (cap cur acc : List Bool) :
    saved (state cap cur acc) = acc := by simp [saved,state,unpairB_pairB]
private theorem budget_state (cap cur acc : List Bool) :
    budget (state cap cur acc) = cap := by simp [budget,state,unpairB_pairB]

private theorem step_cpt {pos neg : List Bool × List Bool → List Bool}
    {light : List Bool → Bool}
    (hp : ComputableInPolyTime encodePair (fun x : List Bool => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : List Bool => x) neg)
    (hl : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool light) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (stateStep pos neg light) := by
  have hx := cpt_unpairB1_1 cpt_unpairB2
  have ha := cpt_unpairB2_1 cpt_unpairB2
  have hc := cpt_unpairB1
  have hk := cpt_tail1 (cpt_tail1 (cpt_comp hx cpt_headI))
  have hpair := cpt_pair hk hx
  have hpos := cpt_comp hpair hp
  have hneg := cpt_comp hpair hn
  have hflag := cpt_bitFlag (cpt_comp hpos hl)
  have hcur := cpt_tk hc (cpt_sel hflag hneg hpos)
  have hacc := cpt_tk hc (cpt_app2 ha (cpt_sel hflag (cpt_const []) hk))
  refine cptE (cpt_sel hx cpt_id (cpt_pairB2 hc (cpt_pairB2 hcur hacc))) (fun s => ?_)
  unfold stateStep state
  change sel (current s) s
    (pairB (budget s) (pairB
      (tk (budget s) (sel (if light (pos (key (current s),current s)) then [true] else [])
        (neg (key (current s),current s)) (pos (key (current s),current s))))
      (tk (budget s) (saved s ++ sel (if light (pos (key (current s),current s)) then [true] else [])
        [] (key (current s)))))) = _
  cases hxs : current s with
  | nil => simp [sel,hxs]
  | cons a as =>
      have hne : a :: as ≠ ([] : List Bool) := List.cons_ne_nil _ _
      cases hb : light (pos (key (a :: as),a :: as)) <;> simp [sel,hne,hb]

private def measure (s : List Bool) : ℕ := 5*(budget s).length+3

private theorem step_measure (pos neg light) (s : List Bool) :
    measure (stateStep pos neg light s) ≤ measure s := by
  dsimp only [stateStep,measure]
  split <;> simp [budget_state]

private theorem step_size (pos neg light) (s : List Bool) :
    (stateStep pos neg light s).length ≤ s.length+measure s := by
  dsimp only [stateStep]
  split
  · omega
  · unfold state measure
    simp only [pairB_length]
    have h1 := tk_length (budget s)
      (if light (pos (key (current s),current s)) then pos (key (current s),current s)
        else neg (key (current s),current s))
    have h2 := tk_length (budget s)
      (saved s ++ if light (pos (key (current s),current s)) then key (current s) else [])
    omega

private theorem measure_bound (s : List Bool) : measure s ≤ 5*s.length+5 := by
  have h := unpairB_length s
  unfold measure budget
  omega

private def vars (φ : CNF) : List ℕ := φ.flatMap (fun c => c.map Prod.fst)

private theorem vars_restrict (φ : CNF) (x : ℕ) (b : Bool) {y : ℕ}
    (h : y ∈ vars (restrict x b φ)) : y ∈ vars φ ∧ y ≠ x := by
  simp only [vars,List.mem_flatMap,List.mem_map,List.mem_filter,restrict,decide_eq_true_eq] at h ⊢
  obtain ⟨d,⟨c,⟨hc,_⟩,he⟩,l,hl,rfl⟩ := h
  rw [← he,List.mem_filter,decide_eq_true_eq] at hl
  exact ⟨⟨c,hc,l,hl.1,rfl⟩,hl.2⟩

private theorem key_spec (l : Literal) (c : Clause) (φ : CNF) :
    key (encodeCNF ((l :: c) :: φ)) = vcode l.1 := by
  have h : encodeCNF ((l :: c) :: φ) = encodeLiteral l ++ (encodeClause c ++ encodeCNF φ) := by
    simp [encodeClause,encodeCNF,List.append_assoc]
  unfold key
  rw [h,headI_lit,encodeLiteral_eq]
  rfl

private theorem key_size (l : Literal) (c : Clause) (φ : CNF) :
    (vcode l.1).length ≤ (encodeCNF ((l :: c) :: φ)).length := by
  have h : encodeCNF ((l :: c) :: φ) = encodeLiteral l ++ (encodeClause c ++ encodeCNF φ) := by
    simp [encodeClause,encodeCNF,List.append_assoc]
  rw [h,encodeLiteral_eq]
  simp only [List.cons_append,List.length_cons,List.length_append]
  omega

private def chosen (x : ℕ) (b : Bool) : List ℕ := if b then [x] else []

private theorem assignment_lift (l : Literal) (c : Clause) (φ : CNF) (b : Bool) (xs : List ℕ)
    (hne : l.1 ∉ xs)
    (he : CNF.eval (fun x => decide (x ∈ xs)) (restrict l.1 b ((l :: c) :: φ)) = true) :
    CNF.eval (fun x => decide (x ∈ chosen l.1 b ++ xs)) ((l :: c) :: φ) = true := by
  have hul := restrict_eval_update _ l.1 b _ he
  have hf : (fun x => decide (x ∈ chosen l.1 b ++ xs)) =
      Function.update (fun x => decide (x ∈ xs)) l.1 b := by
    funext x
    by_cases h : x = l.1
    · subst x
      cases b <;> simp [chosen,hne]
    · cases b <;> simp [chosen,h,Function.update_of_ne]
  rw [hf]
  exact hul

private theorem encoded_nonempty (c : Clause) (φ : CNF) : encodeCNF (c :: φ) ≠ [] := by
  have h : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
  rw [h]
  simp [encodeClause]

private theorem run {pos neg : List Bool × List Bool → List Bool} {light : List Bool → Bool}
    (hp : ∀ x φ, pos (vcode x,encodeCNF φ) = encodeCNF (restrict x true φ))
    (hn : ∀ x φ, neg (vcode x,encodeCNF φ) = encodeCNF (restrict x false φ))
    (hl : ∀ φ, light (encodeCNF φ) = true ↔ wt φ < 1)
    (cap acc : List Bool) (φ : CNF) (n m : ℕ)
    (h0 : (encodeCNF φ).length ≤ n) (hm : (encodeCNF φ).length ≤ m)
    (hcap : acc.length + n*m ≤ cap.length)
    (hd : ∀ c ∈ φ, (c.map Prod.fst).Nodup) (hw : wt φ < 1) :
    ∃ xs : List ℕ,
      saved ((stateStep pos neg light)^[n] (state cap (encodeCNF φ) acc)) = acc ++ xs.flatMap vcode ∧
      (∀ x ∈ xs, x ∈ vars φ) ∧ CNF.eval (fun x => decide (x ∈ xs)) φ = true := by
  induction n generalizing φ acc with
  | zero =>
      cases φ with
      | nil => exact ⟨[],by simp [saved_state],by simp,rfl⟩
      | cons c φ =>
          have he := encoded_nonempty c φ
          have hh : (encodeCNF (c :: φ)).length = 0 := Nat.eq_zero_of_le_zero h0
          exact (he (List.length_eq_zero_iff.mp hh)).elim
  | succ n ih =>
      cases φ with
      | nil =>
          have hstep : stateStep pos neg light (state cap (encodeCNF []) acc) =
              state cap (encodeCNF []) acc := by simp [stateStep,current_state,encodeCNF]
          have he : ∀ i, (stateStep pos neg light)^[i] (state cap (encodeCNF []) acc) =
              state cap (encodeCNF []) acc := by
            intro i
            induction i with
            | zero => rfl
            | succ i ih => rw [Function.iterate_succ_apply,hstep,ih]
          exact ⟨[],by simp [he,saved_state],by simp,rfl⟩
      | cons c φ =>
          cases c with
          | nil => exact (lowWeight_has_first_literal [] φ hw rfl).elim
          | cons l c =>
              let f : CNF := (l :: c) :: φ
              let b := decide (wt (restrict l.1 true f) < 1)
              let next := restrict l.1 b f
              have hbit : light (encodeCNF (restrict l.1 true f)) = b := by
                have h := hl (restrict l.1 true f)
                by_cases e : wt (restrict l.1 true f) < 1
                · simpa [b,e] using h.mpr e
                · have hf : light (encodeCNF (restrict l.1 true f)) = false := by
                    cases hb : light (encodeCNF (restrict l.1 true f)) with
                    | false => rfl
                    | true => exact (e (h.mp hb)).elim
                  simpa [b,e] using hf
              have hnd := lowWeight_restrict f l.1 hd hw
              have hlt : (encodeCNF next).length < (encodeCNF f).length := restrict_encoding_lt l c φ b
              have hn' : (encodeCNF next).length ≤ n := by
                change (encodeCNF f).length ≤ n+1 at h0
                omega
              have hm' : (encodeCNF next).length ≤ m := hlt.le.trans hm
              have hk : (vcode l.1).length ≤ m := (key_size l c φ).trans hm
              let acc' := acc ++ (chosen l.1 b).flatMap vcode
              have hacc : acc'.length ≤ acc.length+m := by
                by_cases hb : b = true
                · simp [acc',chosen,hb,hk]
                · simp [acc',chosen,hb]
              have hcap' : acc'.length + n*m ≤ cap.length := by
                rw [Nat.succ_mul] at hcap
                omega
              have ht1 : (encodeCNF next).length ≤ cap.length := by
                rw [Nat.succ_mul] at hcap
                omega
              have ht2 : acc'.length ≤ cap.length := by omega
              have he : stateStep pos neg light (state cap (encodeCNF f) acc) =
                  state cap (encodeCNF next) acc' := by
                have hcases : (if b then encodeCNF (restrict l.1 true f) else encodeCNF (restrict l.1 false f)) =
                    encodeCNF next := by
                  change _ = encodeCNF (restrict l.1 b f)
                  by_cases hb : b = true
                  · simp [hb]
                  · have hf : b = false := Bool.eq_false_iff.mpr hb
                    simp [hf]
                have ha : (if b then vcode l.1 else []) = (chosen l.1 b).flatMap vcode := by
                  cases b <;> simp [chosen]
                have hx : key (encodeCNF f) = vcode l.1 := key_spec l c φ
                have hz : encodeCNF f ≠ [] := encoded_nonempty (l :: c) φ
                simp only [stateStep,current_state,saved_state,budget_state,hx,hz,ite_false,hp,hn,hbit,hcases,ha]
                change state cap (tk cap (encodeCNF next)) (tk cap acc') = _
                rw [tk_eq,tk_eq,List.take_of_length_le ht1,List.take_of_length_le ht2]
              obtain ⟨xs,hxs,hsub,hsol⟩ := ih acc' next hn' hm' hcap' (hnd.1 b) hnd.2
              refine ⟨chosen l.1 b ++ xs,?_,?_,?_⟩
              · change saved ((stateStep pos neg light)^[n+1] (state cap (encodeCNF f) acc)) = _
                rw [Function.iterate_succ_apply,he,hxs,List.flatMap_append]
                exact List.append_assoc _ _ _
              · intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · have hx' : x = l.1 := by
                    by_cases hb : b = true <;> simp_all [chosen]
                  subst x
                  exact List.mem_flatMap.mpr ⟨l :: c,List.mem_cons_self,List.mem_map.mpr ⟨l,List.mem_cons_self,rfl⟩⟩
                · exact (vars_restrict f l.1 b (hsub x hx)).1
              · apply assignment_lift l c φ b xs _ hsol
                intro hx
                exact (vars_restrict f l.1 b (hsub l.1 hx)).2 rfl

/-- The measured branch-by-weight algorithm emits a sparse assignment for every
canonical CNF of weight below one and without repeated variables in a clause. -/
theorem MeasuredLowWeightSearch :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF,
        (∀ c ∈ φ, (c.map Prod.fst).Nodup) →
        (φ.map (fun c => (2 : ℚ)⁻¹ ^ c.length)).sum < 1 →
        ∃ xs : List ℕ,
          search (encodeCNF φ) = xs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (∀ x ∈ xs, ∃ c ∈ φ, ∃ l ∈ c, l.1 = x) ∧
          CNF.eval (fun x => decide (x ∈ xs)) φ = true := by
  obtain ⟨pos,hpos,hps⟩ := MeasuredVariableRestriction (some true)
  obtain ⟨neg,hneg,hns⟩ := MeasuredVariableRestriction (some false)
  obtain ⟨light,hlight,hls⟩ := MeasuredClauseWeight
  let cap := fun x : List Bool => mulU x x
  let initial := fun x : List Bool => state (cap x) x []
  let search := fun x : List Bool => saved ((stateStep pos neg light)^[x.length] (initial x))
  have hi : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) initial :=
    cpt_pairB2 (cpt_mulU2 cpt_id cpt_id) (cpt_pairB2 cpt_id (cpt_const []))
  have ht := cpt_iterMeasure (step_cpt hpos hneg hlight) measure 5 (step_measure pos neg light)
    (step_size pos neg light) measure_bound cpt_id hi
  have hs : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search :=
    cpt_unpairB2_1 (cpt_unpairB2_1 ht)
  refine ⟨search,hs,fun φ hd hw => ?_⟩
  let x := encodeCNF φ
  have hc : ([] : List Bool).length + x.length*x.length ≤ (cap x).length := by
    simp [cap,mulU,un]
  obtain ⟨xs,he,hv,hgood⟩ := run (pos := pos) (neg := neg) (light := light)
    hps hns hls (cap x) [] φ x.length x.length (Nat.le_refl _) (Nat.le_refl _) hc hd hw
  refine ⟨xs,?_,?_,hgood⟩
  · change saved ((stateStep pos neg light)^[x.length] (state (cap x) (encodeCNF φ) [])) = xs.flatMap vcode
    simpa only [List.nil_append] using he
  · intro i hi
    have hm := hv i hi
    simpa only [vars,List.mem_flatMap,List.mem_map] using hm

end PEqualNP.Outside
