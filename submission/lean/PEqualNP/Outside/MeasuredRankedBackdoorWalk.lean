import PEqualNP.Outside.BackdoorRank
import PEqualNP.Outside.CNFWideClausePacking
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

private def wide (pack : Raw → Raw) (s : Raw) : Raw := (unpairB (pack (shape s))).2
private def key (w : Raw) : Raw := (headI w).tail.tail
private def digit (dv : Div) (v : Raw) : Raw × Raw := dv (v,un 6)
private def keyAt (d w : Raw) : Raw :=
  if d = [] ∨ d = un 3 then key w
  else if d = un 1 ∨ d = un 4 then key (dropI w)
  else key (dropI (dropI w))

private def walkStep (pack : Raw → Raw) (div : Div) (erase pos neg : Change) (s : Raw) : Raw :=
  let w := wide pack s
  let cb := (digit div (credit s)).1
  let qd := digit div (rank s)
  let x := keyAt qd.2 w
  let ψ := (x,residual s)
  let z := cap s
  if w = [] ∨ cb = [] then s else
    state z (tk z cb) (tk z qd.1) (tk z (erase (x,shape s)))
      (tk z (if qd.2.tail.tail = [] then pos ψ else neg ψ))

private def measure (s : Raw) : ℕ := 9*(cap s).length+5

private theorem measure_step (pack div erase pos neg) (s : Raw) :
    measure (walkStep pack div erase pos neg s) ≤ measure s := by
  dsimp only [walkStep,measure]
  split
  · omega
  · rw [(projections _ _ _ _ _).1]

private theorem length_step (pack div erase pos neg) (s : Raw) :
    (walkStep pack div erase pos neg s).length ≤ s.length+measure s := by
  dsimp only [walkStep]
  split
  · omega
  · simp only [state,measure,pairB_length]
    have hb := tk_length (cap s) (digit div (credit s)).1
    have hj := tk_length (cap s) (digit div (rank s)).1
    have he := tk_length (cap s) (erase (keyAt (digit div (rank s)).2 (wide pack s),shape s))
    have hp := tk_length (cap s) (if (digit div (rank s)).2.tail.tail = [] then
      pos (keyAt (digit div (rank s)).2 (wide pack s),residual s)
      else neg (keyAt (digit div (rank s)).2 (wide pack s),residual s))
    omega

private theorem measure_bound (s : Raw) : measure s ≤ 9*s.length+9 := by
  have h := unpairB_length s
  unfold measure cap
  omega

private theorem keyAt_cpt {d w : Raw → Raw}
    (hd : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) d)
    (hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) w) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => keyAt (d s) (w s)) := by
  have hkey {f : Raw → Raw}
      (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f) :
      ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => key (f s)) :=
    cpt_tail1 (cpt_tail1 (cpt_comp hf cpt_headI))
  have hw₁ := cpt_comp hw cpt_dropI
  have hw₂ := cpt_comp hw₁ cpt_dropI
  have hfirst := hkey hw
  have hsecond := hkey hw₁
  have hthird := hkey hw₂
  have e1 := cpt_eqF hd (cpt_const (un 1))
  have e3 := cpt_eqF hd (cpt_const (un 3))
  have e4 := cpt_eqF hd (cpt_const (un 4))
  refine cptE (cpt_sel hd hfirst (cpt_sel e3 (cpt_sel e1 (cpt_sel e4 hthird hsecond) hsecond) hfirst))
    (fun s => ?_)
  dsimp only [keyAt]
  by_cases h0 : d s = [] <;> by_cases h3 : d s = un 3 <;> by_cases h1 : d s = un 1 <;>
    by_cases h4 : d s = un 4 <;> simp [sel,bflag,h0,h3,h1,h4] <;> simp_all [un]

private theorem step_cpt {pack : Raw → Raw} {div : Div} {erase pos neg : Change}
    (hw : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) pack)
    (hd : ComputableInPolyTime encodePair encodePair div)
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) erase)
    (hp : ComputableInPolyTime encodePair (fun x : Raw => x) pos)
    (hn : ComputableInPolyTime encodePair (fun x : Raw => x) neg) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (walkStep pack div erase pos neg) := by
  have hz := cpt_unpairB1
  have hb := cpt_unpairB1_1 cpt_unpairB2
  have hac := cpt_unpairB2_1 cpt_unpairB2
  have hj := cpt_unpairB1_1 hac
  have hfs := cpt_unpairB2_1 hac
  have hs := cpt_unpairB1_1 hfs
  have hr := cpt_unpairB2_1 hfs
  have hu : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (wide pack) :=
    cpt_unpairB2_1 (cpt_comp hs hw)
  have hdiv {f : Raw → Raw}
      (hf : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) f) :
      ComputableInPolyTime (fun x : Raw => x) encodePair (fun s => digit div (f s)) :=
    cpt_comp (g := div) (cpt_pair hf (cpt_const (un 6))) hd
  have hcb := cpt_comp (hdiv hb) cpt_fst
  have hq := cpt_comp (hdiv hj) cpt_fst
  have hd' := cpt_comp (hdiv hj) cpt_snd
  have hx := keyAt_cpt hd' hu
  have hsh := cpt_comp (cpt_pair hx hs) he
  have hψ := cpt_pair hx hr
  have hpos := cpt_comp hψ hp
  have hneg := cpt_comp hψ hn
  have hsign := cpt_tail1 (cpt_tail1 hd')
  have hnext := cpt_pairB2 hz (cpt_pairB2 (cpt_tk hz hcb) (cpt_pairB2 (cpt_tk hz hq)
    (cpt_pairB2 (cpt_tk hz hsh) (cpt_tk hz (cpt_sel hsign hpos hneg)))))
  refine cptE (cpt_sel hu cpt_id (cpt_sel hcb cpt_id hnext)) (fun s => ?_)
  change sel (wide pack s) s (sel (digit div (credit s)).1 s _) = _
  simp only [walkStep,sel,state]
  by_cases hA : wide pack s = [] <;> by_cases hB : (digit div (credit s)).1 = [] <;> simp [hA,hB] <;> rfl


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

private theorem coded_cons (l : Literal) (c : Clause) (φ : CNF) :
    encodeCNF ((l :: c) :: φ) = encodeLiteral l ++ (encodeClause c ++ encodeCNF φ) := by
  simp [encodeCNF,encodeClause,List.append_assoc]

private theorem key_head (l : Literal) (c : Clause) (φ : CNF) :
    key (encodeCNF ((l :: c) :: φ)) = vcode l.1 := by
  unfold key
  rw [coded_cons,headI_lit,encodeLiteral_eq]
  rfl

private theorem drop_head (l : Literal) (c : Clause) (φ : CNF) :
    dropI (encodeCNF ((l :: c) :: φ)) = encodeCNF (c :: φ) := by
  rw [coded_cons,dropI_lit]
  simp [encodeCNF]

private theorem canonical_key (d : ℕ) (hd : d < 6) (l₁ l₂ l₃ : Literal) (c : Clause) (φ : CNF) :
    keyAt (un d) (encodeCNF ((l₁ :: l₂ :: l₃ :: c) :: φ)) = vcode (rankedKey l₁ l₂ l₃ d) := by
  interval_cases d <;> simp [keyAt,rankedKey,un,drop_head,key_head]

private theorem canonical_sign (d : ℕ) (hd : d < 6) :
    (un d).tail.tail = [] ↔ rankedPolarity d = true := by
  interval_cases d <;> decide

private theorem wide_shape (φ : CNF) :
    ((φ.filter (fun c => 2 < c.length)).reverse = [] ↔ IsKCNF 2 φ) ∧
    ∀ a b c, backdoorPick φ = some (a,b,c) →
      ∃ r ds, (φ.filter (fun c => 2 < c.length)).reverse = (a :: b :: c :: r) :: ds := by
  constructor
  · rw [List.reverse_eq_nil_iff,List.filter_eq_nil_iff]
    simp [IsKCNF,decide_eq_true_eq]
  · intro a b c h
    unfold backdoorPick at h
    split at h
    · rename_i l₁ l₂ l₃ r ds he
      cases h
      exact ⟨r,ds,he⟩
    · contradiction

private def finished (base pack : Raw → Raw) (s : Raw) : Bool :=
  !(sel (wide pack s) (base (residual s)) []).isEmpty

private theorem finished_cpt {base pack : Raw → Raw}
    (hb : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) base)
    (hp : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) pack) :
    ComputableInPolyTime (fun x : Raw => x) Computability.encodeBool (finished base pack) := by
  have hs := cpt_unpairB1_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  have hr := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2))
  have hw := cpt_unpairB2_1 (cpt_comp hs hp)
  exact cpt_comp (g := fun w : Raw => !w.isEmpty)
    (cpt_sel hw (cpt_comp hr hb) (cpt_const [])) bf_cpt_neL

private theorem repeat_fixed (f : Raw → Raw) (s : Raw) (h : f s = s) (n : ℕ) :
    f^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,h,ih]

private theorem walk_correct (pack : Raw → Raw) (div : Div) (erase pos neg : Change) (base : Raw → Raw)
    (hw : ∀ φ, (unpairB (pack (encodeCNF φ))).2 = encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse))
    (hd : ∀ v, digit div v = (un (v.length / 6),un (v.length % 6)))
    (he : ∀ x φ, erase (vcode x,encodeCNF φ) = encodeCNF (eraseVariable x φ))
    (hp : ∀ x φ, pos (vcode x,encodeCNF φ) = encodeCNF (restrict x true φ))
    (hn : ∀ x φ, neg (vcode x,encodeCNF φ) = encodeCNF (restrict x false φ))
    (hb : ∀ φ, IsKCNF 2 φ → (base (encodeCNF φ) ≠ [] ↔ Satisfiable φ))
    (z : Raw) (n B j : ℕ) (φ ψ : CNF) (hsub : ψ.Sublist φ)
    (hB : B ≤ z.length) (hj : j ≤ z.length) (hφ : (encodeCNF φ).length ≤ z.length)
    (hψ : (encodeCNF ψ).length ≤ z.length) :
    finished base pack ((walkStep pack div erase pos neg)^[n]
      (state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ))) = true ↔ rankedWalk n B j φ ψ := by
  induction n generalizing B j φ ψ with
  | zero =>
      let s := state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)
      have hproj : cap s = z ∧ credit s = un B ∧ rank s = un j ∧
          shape s = encodeCNF φ ∧ residual s = encodeCNF ψ :=
        projections z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)
      have hwide : wide pack s = encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse) := by
        unfold wide
        rw [hproj.2.2.2.1,hw]
      have hnil : wide pack s = [] ↔ IsKCNF 2 φ := by
        rw [hwide,← (wide_shape φ).1]
        constructor
        · intro h
          exact encodeCNF_injective (h.trans (show [] = encodeCNF [] by rfl))
        · rintro h
          rw [h]
          rfl
      change finished base pack s = true ↔ IsKCNF 2 φ ∧ Satisfiable ψ
      unfold finished
      rw [hproj.2.2.2.2]
      by_cases hf : IsKCNF 2 φ
      · have h0 := hnil.mpr hf
        simp only [sel,h0,ite_true,Bool.not_eq_true',List.isEmpty_eq_false_iff,hb ψ (width_sublist hsub hf),hf,true_and]
      · have h0 : wide pack s ≠ [] := fun h => hf (hnil.mp h)
        simp [sel,h0,hf]
  | succ n ih =>
      let s := state z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)
      let step := walkStep pack div erase pos neg
      have hproj : cap s = z ∧ credit s = un B ∧ rank s = un j ∧
          shape s = encodeCNF φ ∧ residual s = encodeCNF ψ :=
        projections z (un B) (un j) (encodeCNF φ) (encodeCNF ψ)
      have hwide : wide pack s = encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse) := by
        unfold wide
        rw [hproj.2.2.2.1,hw]
      have hcredit : (digit div (credit s)).1 = un (B/6) := by
        rw [hproj.2.1,hd,un_length]
      have hrank : digit div (rank s) = (un (j/6),un (j%6)) := by
        rw [hproj.2.2.1,hd,un_length]
      have hiter (h : step s = s) :
          finished base pack (step^[n+1] s) = true ↔ finished base pack (step^[n] s) = true := by
        rw [Function.iterate_succ_apply,h]
      change finished base pack (step^[n+1] s) = true ↔ _
      rw [rankedWalk]
      cases hpk : backdoorPick φ with
      | none =>
          have h2 := (backdoor_pick φ).1.mp hpk
          have hz : wide pack s = [] := by rw [hwide,(wide_shape φ).1.mpr h2]; rfl
          have hs : step s = s := by simp [step,walkStep,hz]
          rw [repeat_fixed step s hs]
          simp only [finished,sel,hz,ite_true,hproj.2.2.2.2,Bool.not_eq_true',List.isEmpty_eq_false_iff]
          exact hb ψ (width_sublist hsub h2)
      | some picked =>
          obtain ⟨l₁,l₂,l₃⟩ := picked
          obtain ⟨r,fs,hfull⟩ := (wide_shape φ).2 _ _ _ hpk
          have hpart := hwide.trans (congrArg encodeCNF hfull)
          have hnon : wide pack s ≠ [] := by
            intro h
            have he := encodeCNF_injective (hpart.symm.trans (h.trans (show [] = encodeCNF [] by rfl)))
            contradiction
          by_cases halt : 6 ≤ B
          · let x := rankedKey l₁ l₂ l₃ (j%6)
            let b := rankedPolarity (j%6)
            have hm : j % 6 < 6 := Nat.mod_lt j (by decide)
            have hkey : keyAt (un (j % 6)) (wide pack s) = vcode x := by
              rw [hpart,canonical_key _ hm]
            have hB' : B/6 ≤ z.length := (Nat.div_le_self _ _).trans hB
            have hj' : j/6 ≤ z.length := (Nat.div_le_self _ _).trans hj
            have he' := (erase_length x φ).trans hφ
            have hr' := (restrict_encoding_le x b ψ).trans hψ
            have ht : un (B/6) ≠ [] := by
              have h : B/6 ≠ 0 := by omega
              simpa [un] using h
            have hbranch :
                (if (un (j%6)).tail.tail = [] then pos (vcode x,encodeCNF ψ) else neg (vcode x,encodeCNF ψ)) =
                  encodeCNF (restrict x b ψ) := by
              have hc : (un (j%6)).tail.tail = [] ↔ b = true := canonical_sign _ hm
              cases hb' : b with
              | false =>
                  have hh : (un (j%6)).tail.tail ≠ [] := by simp [hb'] at hc; exact hc
                  simp [hh,hb',hn]
              | true =>
                  have hh := hc.mpr hb'
                  simp [hh,hb',hp]
            have hstep : step s = state z (un (B/6)) (un (j/6)) (encodeCNF (eraseVariable x φ))
                (encodeCNF (restrict x b ψ)) := by
              simp only [step,walkStep,hcredit,hrank,hnon,ht,or_self,ite_false,hkey,hproj.1,hproj.2.2.2.1,
                hproj.2.2.2.2,he,hbranch,tk_eq]
              have ht1 : (un (B/6)).length ≤ z.length := by simpa only [un_length] using hB'
              have ht2 : (un (j/6)).length ≤ z.length := by simpa only [un_length] using hj'
              rw [List.take_of_length_le ht1,List.take_of_length_le ht2,List.take_of_length_le he',List.take_of_length_le hr']
            rw [Function.iterate_succ_apply,hstep]
            simp only [halt,true_and]
            exact ih _ _ _ _ (restrict_sublist_erase x b hsub) hB' hj' he' hr'
          · have h0 : B/6 = 0 := by omega
            have hs : step s = s := by simp [step,walkStep,hcredit,h0,un]
            rw [repeat_fixed step s hs]
            simp [finished,sel,hnon,halt]

/-- One measured path through the 2-CNF variable-deletion tree, with a unary
node budget. A rank below the budget succeeds exactly on the promised class
when the residual CNF is satisfiable. -/
theorem MeasuredRankedBackdoorWalk :
    ∃ walk : List Bool → Bool,
      ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool walk ∧
      ∀ (limit : List Bool) (φ ψ : CNF), 1 ≤ limit.length → ψ.Sublist φ →
        ((∃ j < limit.length, walk (pairB limit (pairB (List.replicate j true)
          (pairB (encodeCNF φ) (encodeCNF ψ)))) = true) ↔
         (∃ k : ℕ, 6^k ≤ limit.length ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
           IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧ Satisfiable ψ) := by
  obtain ⟨pack,hpack,hparts⟩ := CNFWideClausePacking
  obtain ⟨div,hdiv,hds⟩ := MeasuredUnaryDivMod
  obtain ⟨erase,he,hes⟩ := MeasuredVariableRestriction none
  obtain ⟨pos,hp,hps⟩ := MeasuredVariableRestriction (some true)
  obtain ⟨neg,hn,hns⟩ := MeasuredVariableRestriction (some false)
  obtain ⟨accept,hacc,hc⟩ := L030
  let base := fun x => if accept x then [true] else []
  let num := fun x : Raw => un x.length
  let loop := walkStep pack div erase pos neg
  let init := fun s => state s (num (unpairB s).1) (num (unpairB (unpairB s).2).1)
    (unpairB (unpairB (unpairB s).2).2).1 (unpairB (unpairB (unpairB s).2).2).2
  let walk := fun s => finished base pack (loop^[(unpairB s).1.length] (init s))
  have hnum : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) num := by
    simpa [num,un] using L055 Polynomial.X
  have hq := cpt_unpairB2_1 cpt_unpairB2
  have hi : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) init :=
    cpt_pairB2 cpt_id (cpt_pairB2 (cpt_comp cpt_unpairB1 hnum)
      (cpt_pairB2 (cpt_comp (cpt_unpairB1_1 cpt_unpairB2) hnum)
        (cpt_pairB2 (cpt_unpairB1_1 hq) (cpt_unpairB2_1 hq))))
  have hit := cpt_iterMeasure (step_cpt hpack hdiv he hp hn) measure 9
    (measure_step pack div erase pos neg) (length_step pack div erase pos neg)
    measure_bound cpt_unpairB1 hi
  refine ⟨walk,cpt_comp hit (finished_cpt (cpt_bitFlag hc) hpack),fun limit φ ψ hpos hsub => ?_⟩
  have ht (φ : CNF) : (unpairB (pack (encodeCNF φ))).2 =
      encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse) := by
    rw [hparts]
    change (unpairB (pairB _ _)).2 = _
    rw [unpairB_pairB]
  have hdm (v : Raw) : digit div v = (un (v.length/6),un (v.length%6)) := by
    simpa [digit,un] using hds v (un 6)
  have her (i : ℕ) (p : CNF) : erase (vcode i,encodeCNF p) = encodeCNF (eraseVariable i p) := by
    simpa [vcode,eraseVariable] using hes i p
  have hb (p : CNF) (hq : IsKCNF 2 p) : base (encodeCNF p) ≠ [] ↔ Satisfiable p := by
    have ha : base (encodeCNF p) ≠ [] ↔ accept (encodeCNF p) = true := by
      unfold base
      cases accept (encodeCNF p) <;> decide
    rw [ha,← hacc]
    constructor
    · rintro ⟨r,_,hr,hSat⟩
      exact encodeCNF_injective hr ▸ hSat
    · exact fun hSat => ⟨p,hq,rfl,hSat⟩
  have hrank (j : ℕ) :
      walk (pairB limit (pairB (un j) (pairB (encodeCNF φ) (encodeCNF ψ)))) = true ↔
      rankedWalk limit.length limit.length j φ ψ := by
    let s := pairB limit (pairB (un j) (pairB (encodeCNF φ) (encodeCNF ψ)))
    have hlen : s.length = 2*limit.length+2*j+2*(encodeCNF φ).length+(encodeCNF ψ).length+3 := by
      simp only [s,pairB_length,un_length]
      omega
    have hs : init s = state s (un limit.length) (un j) (encodeCNF φ) (encodeCNF ψ) := by
      simp only [init,s,num,unpairB_pairB,un_length]
    change finished base pack (loop^[(unpairB s).1.length] (init s)) = true ↔ _
    rw [hs,show (unpairB s).1 = limit by simp [s,unpairB_pairB]]
    exact walk_correct pack div erase pos neg base ht hdm her hps hns hb s
      _ _ _ φ ψ hsub (by omega) (by omega) (by omega) (by omega)
  constructor
  · rintro ⟨j,_,hj⟩
    exact ranked_sound _ _ j hpos φ ψ ((hrank j).mp hj)
  · rintro ⟨⟨k,hk,hdoor⟩,hs⟩
    obtain ⟨j,hj,hw⟩ := ranked_complete limit.length limit.length k le_rfl hk φ ψ hdoor hs
    exact ⟨j,hj,(hrank j).mpr hw⟩

end PEqualNP.Outside
