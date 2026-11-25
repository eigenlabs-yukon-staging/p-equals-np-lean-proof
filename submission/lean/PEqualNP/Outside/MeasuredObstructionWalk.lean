import PEqualNP.Outside.ObstructionRank
import PEqualNP.Outside.MeasuredVariableRestriction
import PEqualNP.Outside.MeasuredUnaryDivMod
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private abbrev Raw := List Bool
private abbrev Change := Raw × Raw → Raw
private abbrev Div := Raw × Raw → Raw × Raw

private def cap (s : Raw) := (unpairB s).1
private def credit (s : Raw) := (unpairB (unpairB s).2).1
private def afterCredit (s : Raw) := (unpairB (unpairB s).2).2
private def rank (s : Raw) := (unpairB (afterCredit s)).1
private def formulas (s : Raw) := (unpairB (afterCredit s)).2
private def shape (s : Raw) := (unpairB (formulas s)).1
private def residual (s : Raw) := (unpairB (formulas s)).2
private def state (z t j p r : Raw) := pairB z (pairB t (pairB j (pairB p r)))

private theorem projections (z t j p r : Raw) :
    cap (state z t j p r) = z ∧ credit (state z t j p r) = t ∧ rank (state z t j p r) = j ∧
    shape (state z t j p r) = p ∧ residual (state z t j p r) = r := by
  simp [cap,credit,rank,shape,residual,state,afterCredit,formulas,unpairB_pairB]

private def keys (pick : Raw → Raw) (s : Raw) : Raw := pick (shape s)
private def key (w : Raw) : Raw := (headI w).tail.tail
private def divide (dv : Div) (a : ℕ) (v : Raw) : Raw × Raw := dv (v,un a)
private def front (w : Raw) : Bool := w.headD false

private def keyAt (d w : Raw) : Raw :=
  let r := dropI^[d.length] w
  key (if front r then r else w)

private def walkStep (pick : Raw → Raw) (div : Div) (a : ℕ) (erase pos neg : Change) (s : Raw) : Raw :=
  let w := keys pick s
  let cb := (divide div (2*a) (credit s)).1
  let qd := divide div (2*a) (rank s)
  let ord := divide div a qd.2
  let x := keyAt ord.2 w
  let ψ := (x,residual s)
  let z := cap s
  if front w = false ∨ cb = [] then s else
    state z (tk z cb) (tk z qd.1) (tk z (erase (x,shape s)))
      (tk z (if ord.1 = [] then pos ψ else neg ψ))

private def measure (s : Raw) : ℕ := 9*(cap s).length+5

private theorem measure_step (pick div a erase pos neg) (s : Raw) :
    measure (walkStep pick div a erase pos neg s) ≤ measure s := by
  dsimp only [walkStep,measure]
  split
  · omega
  · rw [(projections _ _ _ _ _).1]

private theorem length_step (pick div a erase pos neg) (s : Raw) :
    (walkStep pick div a erase pos neg s).length ≤ s.length+measure s := by
  dsimp only [walkStep]
  split
  · omega
  · simp only [state,measure,pairB_length]
    let b := (divide div (2*a) (credit s)).1
    let j := divide div (2*a) (rank s)
    let o := divide div a j.2
    let x := keyAt o.2 (keys pick s)
    have hb := tk_length (cap s) b
    have hj := tk_length (cap s) j.1
    have he := tk_length (cap s) (erase (x,shape s))
    have hp := tk_length (cap s) (if o.1 = [] then pos (x,residual s) else neg (x,residual s))
    dsimp only [b,j,o,x] at hb hj he hp
    omega

private theorem measure_bound (s : Raw) : measure s ≤ 9*s.length+9 := by
  have h := unpairB_length s
  unfold measure cap
  omega

private theorem keyAt_cpt {d w : Raw → Raw}
    (hd' : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) d)
    (hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) w) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => keyAt (d s) (w s)) := by
  have hdrop (s : Raw) : (dropI s).length ≤ s.length := dropI_length s
  have hr := cpt_iterLen cpt_dropI hdrop hd' hw
  have hselect := cpt_sel (cpt_hd1 hr) hw hr
  refine cptE (cpt_tail1 (cpt_tail1 (cpt_comp hselect cpt_headI))) (fun s => ?_)
  let r := dropI^[(d s).length] (w s)
  change key (sel (hd r) (w s) r) = key (if front r then r else w s)
  cases r with
  | nil => rfl
  | cons b r => cases b <;> rfl

private theorem step_cpt {pick : Raw → Raw} {div : Div} {erase pos neg : Change}
    (hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) pick)
    (hd' : ComputableInPolyTime encodePair encodePair div)
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hp : ComputableInPolyTime encodePair (fun x : Raw => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : Raw => x) neg) (a : ℕ) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (walkStep pick div a erase pos neg) := by
  have hz := cpt_unpairB1
  have hb := cpt_unpairB1_1 cpt_unpairB2
  have hac := cpt_unpairB2_1 cpt_unpairB2
  have hj := cpt_unpairB1_1 hac
  have hfs := cpt_unpairB2_1 hac
  have hs := cpt_unpairB1_1 hfs
  have hr := cpt_unpairB2_1 hfs
  have hu : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (keys pick) := cpt_comp (g := pick) hs hw
  have hdiv (a : ℕ) {f : Raw → Raw}
      (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f) :
      ComputableInPolyTime (fun x : Raw => x) encodePair (fun s => divide div a (f s)) :=
    cpt_comp (g := div) (cpt_pair hf (cpt_const (un a))) hd'
  have hcb := cpt_comp (hdiv (2*a) hb) cpt_fst
  have hq := cpt_comp (hdiv (2*a) hj) cpt_fst
  have hdigit := cpt_comp (hdiv (2*a) hj) cpt_snd
  have hord := hdiv a hdigit
  have hx := keyAt_cpt (cpt_comp hord cpt_snd) hu
  have hsh := cpt_comp (cpt_pair hx hs) he
  have hψ := cpt_pair hx hr
  have hpos := cpt_comp hψ hp
  have hneg := cpt_comp hψ hn
  have hnext := cpt_pairB2 hz (cpt_pairB2 (cpt_tk hz hcb) (cpt_pairB2 (cpt_tk hz hq)
    (cpt_pairB2 (cpt_tk hz hsh) (cpt_tk hz (cpt_sel (cpt_comp hord cpt_fst) hpos hneg)))))
  refine cptE (cpt_sel (cpt_hd1 hu) cpt_id (cpt_sel hcb cpt_id hnext)) (fun s => ?_)
  change sel (hd (keys pick s)) s (sel (divide div (2*a) (credit s)).1 s _) = _
  dsimp only [walkStep,sel,state]
  have htag : hd (keys pick s) = [] ↔ front (keys pick s) = false := by
    unfold front
    cases keys pick s with
    | nil => decide
    | cons b r => cases b <;> simp [hd]
  by_cases hA : front (keys pick s) = false
  · simp [(htag.mpr hA),hA]
  · by_cases hB : (divide div (2*a) (credit s)).1 = []
    · simp [hA,hB]
    · simp [hA,hB,show hd (keys pick s) ≠ [] from fun h => hA (htag.mp h)]
      rfl

private def keyClause (xs : List ℕ) : Clause := xs.map (fun x => (x,true))

private theorem key_front (xs : List ℕ) :
    front (encodeClause (keyClause xs)) = decide (xs ≠ []) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [front,keyClause,encodeClause,encodeLiteral_eq]

private theorem key_head (x : ℕ) (xs : List ℕ) :
    key (encodeClause (keyClause (x :: xs))) = vcode x := by
  have h : encodeClause (keyClause (x :: xs)) =
      encodeLiteral (x,true) ++ encodeClause (keyClause xs) := by simp [keyClause,encodeClause]
  rw [h]
  unfold key
  rw [headI_lit,encodeLiteral_eq]
  rfl

private theorem raw_drop (xs : List ℕ) (i : ℕ) :
    dropI^[i] (encodeClause (keyClause xs)) = if i ≤ xs.length then encodeClause (keyClause (xs.drop i)) else [] := by
  induction i generalizing xs with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply]
      cases xs with
      | nil =>
          have h : dropI (encodeClause (keyClause [])) = [] := rfl
          rw [h]
          have hir : ¬ i + 1 ≤ ([] : List ℕ).length := by simp
          rw [ite_eq_right hir]
          clear * - i
          induction i with
          | zero => rfl
          | succ i hi => rw [Function.iterate_succ_apply,show dropI [] = [] by rfl,hi]
      | cons x xs =>
          have he : encodeClause (keyClause (x :: xs)) =
              encodeLiteral (x,true) ++ encodeClause (keyClause xs) := by simp [keyClause,encodeClause]
          rw [he,dropI_lit,ih]
          simp

private theorem key_spec (xs : List ℕ) (i : ℕ) (h : xs ≠ []) :
    keyAt (un i) (encodeClause (keyClause xs)) = vcode (chooseRankKey xs i) := by
  unfold keyAt chooseRankKey
  rw [un_length,raw_drop]
  by_cases hp : i < xs.length
  · rw [ite_eq_left hp.le,List.drop_eq_getElem_cons hp,List.getElem?_eq_getElem hp]
    dsimp only
    rw [key_front]
    rw [decide_eq_true (List.cons_ne_nil _ _)]
    simp only [if_pos rfl,Option.getD_some]
    exact key_head _ _
  · have he : xs.length ≤ i := by omega
    rw [List.getElem?_eq_none he]
    have hr : front (if i ≤ xs.length then encodeClause (keyClause (xs.drop i)) else []) = false := by
      by_cases h' : i ≤ xs.length
      · rw [ite_eq_left h',List.drop_eq_nil_of_le he]
        rfl
      · rw [ite_eq_right h']
        rfl
    dsimp only
    simp only [hr,Bool.false_eq_true,ite_false,Option.getD_none]
    cases xs with
    | nil => contradiction
    | cons x xs => exact key_head x xs

private theorem erase_length (x : ℕ) (φ : CNF) :
    (encodeCNF (eraseVariable x φ)).length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      let pred := fun l : Literal => decide (l.1 ≠ x)
      have hh := ((List.filter_sublist (l := c) (p := pred)).flatMap encodeLiteral).length_le
      have he (c : Clause) (φ : CNF) :
          (encodeCNF (c :: φ)).length = (encodeClause c).length + (encodeCNF φ).length := by simp [encodeCNF]
      change (encodeCNF (c.filter pred :: eraseVariable x φ)).length ≤ _
      rw [he,he]
      apply Nat.add_le_add _ ih
      simp only [encodeClause,List.length_append]
      omega

private theorem rank_sign (a d : ℕ) (ha : 0 < a) :
    un (d/a) = [] ↔ d < a := by
  have h : un (d/a) = [] ↔ d/a = 0 := by simp [un]
  rw [h]
  constructor
  · intro hz
    by_contra hlt
    have hpos := Nat.div_pos (le_of_not_gt hlt) ha
    omega
  · exact fun h => Nat.div_eq_of_lt h

private def finished (base pick : Raw → Raw) (s : Raw) : Bool :=
  !(sel (hd (keys pick s)) (base (residual s)) []).isEmpty

private theorem finished_cpt {base pick : Raw → Raw}
    (hb : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) base)
    (hp : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) pick) :
    ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool (finished base pick) := by
  have hf := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  have hs := cpt_unpairB1_1 hf
  have hr := cpt_unpairB2_1 hf
  exact cpt_comp (g := fun w : Raw => !w.isEmpty)
    (cpt_sel (cpt_hd1 (cpt_comp (g := pick) hs hp)) (cpt_comp hr hb) (cpt_const [])) bf_cpt_neL

private theorem repeat_fixed (f : Raw → Raw) (s : Raw) (h : f s = s) (n : ℕ) :
    f^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,h,ih]

private theorem head_flag (w : Raw) : hd w = [] ↔ front w = false := by
  unfold front
  cases w with
  | nil => decide
  | cons b w => cases b <;> simp [hd]

private theorem walk_correct (A : CNF → Prop) (select : CNF → List ℕ) (a : ℕ) (ha : 0 < a)
    (pick : Raw → Raw) (div : Div) (erase pos neg : Change) (base : Raw → Raw)
    (hw : ∀ φ, pick (encodeCNF φ) = encodeClause (keyClause (select φ)))
    (hc : ∀ φ, select φ = [] ↔ A φ)
    (hdiv : ∀ a v, divide div a v = (un (v.length / a),un (v.length % a)))
    (he : ∀ x φ, erase (vcode x,encodeCNF φ) = encodeCNF (eraseVariable x φ))
    (hp : ∀ x φ, pos (vcode x,encodeCNF φ) = encodeCNF (restrict x true φ))
    (hn : ∀ x φ, neg (vcode x,encodeCNF φ) = encodeCNF (restrict x false φ))
    (hb : ∀ φ ψ, ψ.Sublist φ → A φ → (base (encodeCNF ψ) ≠ [] ↔ Satisfiable ψ))
    (z : Raw) (n B j : ℕ) (φ ψ : CNF) (hsub : ψ.Sublist φ)
    (hB : B ≤ z.length) (hj : j ≤ z.length) (hφ : (encodeCNF φ).length ≤ z.length)
    (hψ : (encodeCNF ψ).length ≤ z.length) :
    finished base pick ((walkStep pick div a erase pos neg)^[n]
      (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ))) = true ↔
      obstructionWalk A select a n B j φ ψ := by
  have hf (B j : ℕ) (φ ψ : CNF) :
      keys pick (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)) = encodeClause (keyClause (select φ)) := by
    unfold keys
    rw [(projections _ _ _ _ _).2.2.2.1,hw]
  have hfinish (B j : ℕ) (φ ψ : CNF) (hs : ψ.Sublist φ) :
      finished base pick (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)) = true ↔
      A φ ∧ Satisfiable ψ := by
    unfold finished
    rw [(projections _ _ _ _ _).2.2.2.2]
    by_cases h : select φ = []
    · have hA := (hc φ).mp h
      have hz : hd (keys pick (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ))) = [] :=
        (head_flag _).mpr (by simp [hf,key_front,h])
      simp only [sel,hz,ite_true,Bool.not_eq_true',List.isEmpty_eq_false_iff,hb φ ψ hs hA,hA,true_and]
    · have hA : ¬ A φ := fun h' => h ((hc φ).mpr h')
      have hn : hd (keys pick (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ))) ≠ [] := by
        rw [ne_eq,head_flag,hf,key_front]
        simp [h]
      simp [sel,hn,hA]
  induction n generalizing B j φ ψ with
  | zero => exact hfinish B j φ ψ hsub
  | succ n ih =>
      let s := state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)
      let step := walkStep pick div a erase pos neg
      have hproj : cap s = z ∧ credit s = un B ∧ rank s = un j ∧
          shape s = encodeCNF φ ∧ residual s = encodeCNF ψ :=
        projections z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)
      have htag : front (keys pick s) = decide (select φ ≠ []) := by
        change front (keys pick (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ))) = _
        rw [hf,key_front]
      have hcredit : (divide div (2*a) (credit s)).1 = un (B/(2*a)) := by
        rw [hproj.2.1,hdiv,un_length]
      have hrank : divide div (2*a) (rank s) = (un (j/(2*a)),un (j%(2*a))) := by
        rw [hproj.2.2.1,hdiv,un_length]
      change finished base pick (step^[n+1] s) = true ↔ _
      by_cases hz : select φ = []
      · have hA := (hc φ).mp hz
        have hs : step s = s := by simp [step,walkStep,htag,hz]
        rw [repeat_fixed step s hs]
        simpa only [obstructionWalk,hz,ite_true,hA,true_and] using hfinish B j φ ψ hsub
      · have hnon : ¬ A φ := fun h => hz ((hc φ).mpr h)
        by_cases hlim : 2*a ≤ B
        · let d := j%(2*a)
          let x := chooseRankKey (select φ) (d%a)
          let b := decide (d < a)
          have hkey : keyAt (un (d%a)) (keys pick s) = vcode x := by
            change keyAt (un (d%a)) (keys pick (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ))) = _
            rw [hf,key_spec _ _ hz]
          have hat : 0 < 2*a := by omega
          have ht : un (B/(2*a)) ≠ [] := by
            have h := Nat.div_pos hlim hat
            simp [un,show B/(2*a) ≠ 0 by omega]
          have hbranch :
              (if un (d/a) = [] then pos (vcode x,encodeCNF ψ) else neg (vcode x,encodeCNF ψ)) =
                encodeCNF (restrict x b ψ) := by
            have hs := rank_sign a d ha
            by_cases h : d < a
            · simp [hs.mpr h,b,h,hp]
            · have hn' : un (d/a) ≠ [] := fun h' => h (hs.mp h')
              simp [hn',b,h,hn]
          have ho : divide div a (un d) = (un (d/a),un (d%a)) := by rw [hdiv,un_length]
          have hb' : B/(2*a) ≤ z.length := (Nat.div_le_self _ _).trans hB
          have hj' : j/(2*a) ≤ z.length := (Nat.div_le_self _ _).trans hj
          have he' := (erase_length x φ).trans hφ
          have hr' := (restrict_encoding_le x b ψ).trans hψ
          have hstep : step s = state z (un (B/(2*a))) (un (j/(2*a)))
              (encodeCNF (eraseVariable x φ)) (encodeCNF (restrict x b ψ)) := by
            have hor : divide div a (un (j%(2*a))) = (un (d/a),un (d%a)) := ho
            have htag' : front (keys pick s) = true := htag.trans (decide_eq_true hz)
            simp only [step,walkStep,htag',Bool.true_eq_false,hcredit,ht,
              hrank,hor,or_self,ite_false,hkey,hproj.1,hproj.2.2.2.1,hproj.2.2.2.2,he,hbranch,tk_eq]
            have h1 : (un (B/(2*a))).length ≤ z.length := by simpa only [un_length] using hb'
            have h2 : (un (j/(2*a))).length ≤ z.length := by simpa only [un_length] using hj'
            rw [List.take_of_length_le h1,List.take_of_length_le h2,List.take_of_length_le he',List.take_of_length_le hr']
          rw [Function.iterate_succ_apply,hstep]
          simp only [obstructionWalk,hz,ite_false,hlim,true_and]
          exact ih _ _ _ _ (restrict_sublist_erase x b hsub) hb' hj' he' hr'
        · have h0 := Nat.div_eq_of_lt (lt_of_not_ge hlim)
          have hs : step s = s := by simp [step,walkStep,hcredit,h0,un]
          rw [repeat_fixed step s hs]
          simpa only [obstructionWalk,hz,ite_false,hlim,false_and,hnon] using hfinish B j φ ψ hsub

/-- A bounded measured obstruction supplies a polynomial-time path verifier.
An accepting rank exists exactly when a deletion backdoor fits the rank
budget and the residual CNF is satisfiable. -/
theorem MeasuredObstructionWalk (G D : Language Bool) (hD : D ∈ P)
    (hsub : ∀ φ ψ : CNF, ψ.Sublist φ → encodeCNF φ ∈ G → encodeCNF ψ ∈ G)
    (hsat : ∀ ψ : CNF, encodeCNF ψ ∈ G → (encodeCNF ψ ∈ D ↔ Satisfiable ψ))
    (a : ℕ) (ha : 0 < a) (select : CNF → List ℕ) (pick : List Bool → List Bool)
    (hpick : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pick)
    (hpickSpec : ∀ φ : CNF, pick (encodeCNF φ) = encodeClause ((select φ).map (fun x => (x,true))))
    (hclear : ∀ φ : CNF, select φ = [] ↔ encodeCNF φ ∈ G)
    (hwidth : ∀ φ : CNF, (select φ).length ≤ a)
    (hhit : ∀ (φ : CNF) (xs : List ℕ), encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G →
      select φ ≠ [] → ∃ x ∈ select φ, x ∈ xs) :
    let pair := fun (p q : List Bool) => List.replicate p.length true ++ false :: (p ++ q)
    ∃ walk : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool walk ∧
      ∀ (limit : List Bool) (φ ψ : CNF), 1 ≤ limit.length → ψ.Sublist φ →
        ((∃ j < limit.length, walk (pair limit (pair (List.replicate j true)
          (pair (encodeCNF φ) (encodeCNF ψ)))) = true) ↔
         (∃ k : ℕ, (2*a)^k ≤ limit.length ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
           encodeCNF (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) ∈ G) ∧ Satisfiable ψ) := by
  obtain ⟨div,hdiv,hds⟩ := MeasuredUnaryDivMod
  obtain ⟨erase,he,hes⟩ := MeasuredVariableRestriction none
  obtain ⟨pos,hp,hps⟩ := MeasuredVariableRestriction (some true)
  obtain ⟨neg,hn,hns⟩ := MeasuredVariableRestriction (some false)
  obtain ⟨accept,hacc,hc⟩ := hD
  let A := fun φ : CNF => encodeCNF φ ∈ G
  let base := fun x => if accept x then [true] else []
  let num := fun x : Raw => un x.length
  let loop := walkStep pick div a erase pos neg
  let init := fun s => state s (num (unpairB s).1) (num (unpairB (unpairB s).2).1)
    (unpairB (unpairB (unpairB s).2).2).1 (unpairB (unpairB (unpairB s).2).2).2
  let walk := fun s => finished base pick (loop^[(unpairB s).1.length] (init s))
  have hnum : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) num := by
    simpa [num,un] using L055 Polynomial.X
  have hq := cpt_unpairB2_1 cpt_unpairB2
  have hi : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) init :=
    cpt_pairB2 cpt_id (cpt_pairB2 (cpt_comp cpt_unpairB1 hnum)
      (cpt_pairB2 (cpt_comp (cpt_unpairB1_1 cpt_unpairB2) hnum)
        (cpt_pairB2 (cpt_unpairB1_1 hq) (cpt_unpairB2_1 hq))))
  have hit := cpt_iterMeasure (step_cpt hpick hdiv he hp hn a) measure 9
    (measure_step pick div a erase pos neg) (length_step pick div a erase pos neg)
    measure_bound cpt_unpairB1 hi
  refine ⟨walk,cpt_comp hit (finished_cpt (cpt_bitFlag hc) hpick),fun limit φ ψ hpos hsub' => ?_⟩
  have hdm (b : ℕ) (v : Raw) : divide div b v = (un (v.length/b),un (v.length%b)) := by
    simpa [divide,un] using hds v (un b)
  have her (i : ℕ) (p : CNF) : erase (vcode i,encodeCNF p) = encodeCNF (eraseVariable i p) := by
    simpa [vcode,eraseVariable] using hes i p
  have hb (p r : CNF) (h : r.Sublist p) (hA : A p) : base (encodeCNF r) ≠ [] ↔ Satisfiable r := by
    have ha : base (encodeCNF r) ≠ [] ↔ accept (encodeCNF r) = true := by
      unfold base
      cases accept (encodeCNF r) <;> decide
    rw [ha,← hacc]
    exact hsat r (hsub p r h hA)
  have hrank (j : ℕ) :
      walk (pairB limit (pairB (un j) (pairB (encodeCNF φ) (encodeCNF ψ)))) = true ↔
      obstructionWalk A select a limit.length limit.length j φ ψ := by
    let s := pairB limit (pairB (un j) (pairB (encodeCNF φ) (encodeCNF ψ)))
    have hlen : s.length = 2*limit.length+2*j+2*(encodeCNF φ).length+(encodeCNF ψ).length+3 := by
      simp only [s,pairB_length,un_length]
      omega
    have hs : init s = state s (un limit.length) (un j) (encodeCNF φ) (encodeCNF ψ) := by
      simp only [init,s,num,unpairB_pairB,un_length]
    change finished base pick (loop^[(unpairB s).1.length] (init s)) = true ↔ _
    rw [hs,show (unpairB s).1 = limit by simp [s,unpairB_pairB]]
    exact walk_correct A select a ha pick div erase pos neg base hpickSpec hclear hdm her hps hns
      hb s _ _ _ φ ψ hsub' (by omega) (by omega) (by omega) (by omega)
  constructor
  · rintro ⟨j,_,hj⟩
    exact obstruction_sound A select a ha hclear _ _ j hpos φ ψ ((hrank j).mp hj)
  · rintro ⟨⟨k,hk,hdoor⟩,hs⟩
    obtain ⟨j,hj,hw⟩ := obstruction_complete A select a ha hclear hhit hwidth
      limit.length limit.length k le_rfl hk φ ψ hdoor hs
    exact ⟨j,hj,(hrank j).mpr hw⟩

end PEqualNP.Outside
