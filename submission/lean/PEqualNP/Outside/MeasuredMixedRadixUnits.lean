import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Outside.MeasuredUnaryDivMod
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Outside.MeasuredLiteralChoice
import PEqualNP.Outside.MeasuredClauseLiteralCount

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def branch : CNF → ℕ → CNF
  | [], _ => []
  | c :: cs, n => (getElem? c (n % c.length)).toList :: branch cs (n / c.length)

private theorem encode_cons (c : Clause) (cs : CNF) :
    encodeCNF (c :: cs) = encodeClause c ++ encodeCNF cs := by simp [encodeCNF]

private theorem choice_len (c : Clause) (i : ℕ) :
    (encodeClause (getElem? c i).toList).length ≤ (encodeClause c).length := by
  induction c generalizing i with
  | nil => simp [encodeClause]
  | cons a c ih =>
      cases i with
      | zero =>
          simp [encodeClause]
      | succ i =>
          have h := ih i
          simp only [List.getElem?_cons_succ]
          refine h.trans ?_
          simp [encodeClause]

private def step (split : List Bool → List Bool × List Bool)
    (count : List Bool → List Bool)
    (divide : List Bool × List Bool → List Bool × List Bool)
    (pick : List Bool × List Bool → List Bool) (s : List Bool) : List Bool :=
  let remaining := (unpairB s).1
  let ix := (unpairB (unpairB s).2).1
  let out := (unpairB (unpairB s).2).2
  let clause := (split remaining).1
  let rest := (split remaining).2
  let qr := divide (ix, count clause)
  if remaining = [] then s
  else pairB rest (pairB qr.1 (out ++ tk clause (pick (qr.2, clause))))

private theorem step_cpt
    {split : List Bool → List Bool × List Bool}
    {count : List Bool → List Bool}
    {divide : List Bool × List Bool → List Bool × List Bool}
    {pick : List Bool × List Bool → List Bool}
    (hs : ComputableInPolyTime (fun x : List Bool => x) encodePair split)
    (hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) count)
    (hd : ComputableInPolyTime encodePair encodePair divide)
    (hp : ComputableInPolyTime encodePair (fun x : List Bool => x) pick) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (step split count divide pick) := by
  have hr := cpt_unpairB1
  have hix := cpt_unpairB1_1 cpt_unpairB2
  have ho := cpt_unpairB2_1 cpt_unpairB2
  have hsplit := cpt_comp hr hs
  have hclause := cpt_comp hsplit cpt_fst
  have hrest := cpt_comp hsplit cpt_snd
  have hqr := cpt_comp (cpt_pair hix (cpt_comp hclause hc)) hd
  have hquo := cpt_comp hqr cpt_fst
  have hrem := cpt_comp hqr cpt_snd
  have hword := cpt_tk hclause (cpt_comp (cpt_pair hrem hclause) hp)
  exact cpt_sel hr cpt_id (cpt_pairB2 hrest (cpt_pairB2 hquo (cpt_app2 ho hword)))

private theorem step_length
    {split : List Bool → List Bool × List Bool}
    {count : List Bool → List Bool}
    {divide : List Bool × List Bool → List Bool × List Bool}
    {pick : List Bool × List Bool → List Bool}
    (hs : ∀ s, (split s).1 ++ (split s).2 = s)
    (hd : ∀ a b : List Bool, divide (a,b) =
      (List.replicate (a.length / b.length) true, List.replicate (a.length % b.length) true))
    (s : List Bool) : (step split count divide pick s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := congrArg List.length (hs (unpairB s).1)
  simp only [List.length_append] at h3
  have h4 := tk_length (split (unpairB s).1).1
    (pick ((divide ((unpairB (unpairB s).2).1, count (split (unpairB s).1).1)).2,
      (split (unpairB s).1).1))
  have h5 : (divide ((unpairB (unpairB s).2).1, count (split (unpairB s).1).1)).1.length ≤
      (unpairB (unpairB s).2).1.length := by
    rw [hd]
    simp only [List.length_replicate]
    exact Nat.div_le_self _ _
  dsimp only [step]
  split
  · omega
  · simp only [pairB_length, List.length_append]
    omega

private theorem run
    {split : List Bool → List Bool × List Bool}
    {count : List Bool → List Bool}
    {divide : List Bool × List Bool → List Bool × List Bool}
    {pick : List Bool × List Bool → List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c, r))
    (hc : ∀ c, count (encodeClause c) = List.replicate c.length true)
    (hd : ∀ a b : List Bool, divide (a,b) =
      (List.replicate (a.length / b.length) true, List.replicate (a.length % b.length) true))
    (hp : ∀ (c : Clause) (i : List Bool),
      pick (i, encodeClause c) = encodeClause (getElem? c i.length).toList)
    (φ : CNF) (ix out : List Bool) (n : ℕ) (hn : φ.length ≤ n) :
    (unpairB (unpairB ((step split count divide pick)^[n]
      (pairB (encodeCNF φ) (pairB ix out)))).2).2 =
      out ++ encodeCNF (branch φ ix.length) := by
  induction n generalizing φ ix out with
  | zero =>
      have e : φ = [] := List.length_eq_zero_iff.mp (by omega)
      subst φ
      simp [branch, encodeCNF, unpairB_pairB]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have hstep : step split count divide pick (pairB (encodeCNF []) (pairB ix out)) =
              pairB (encodeCNF []) (pairB ix out) := by
            simp [step, unpairB_pairB, encodeCNF]
          rw [hstep, ih [] _ _ (by simp)]
      | cons c φ =>
          have he : encodeClause c ++ encodeCNF φ ≠ [] := by simp [encodeClause]
          have ht : φ.length ≤ n := by simpa using hn
          rw [encode_cons]
          simp only [step, unpairB_pairB, hs, hc, hd, hp, List.length_replicate,
            ite_eq_right he]
          rw [tk_eq, List.take_of_length_le (choice_len _ _)]
          rw [ih φ _ _ ht]
          simp only [branch, encode_cons, List.length_replicate, List.append_assoc]

private theorem formula_length (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.length_cons, encode_cons, List.length_append]
      have hc : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

private theorem unit_sat (o : Option Literal) (σ : Assignment) :
    Clause.eval σ o.toList = true ↔ ∃ l, o = some l ∧ Literal.eval σ l = true := by
  cases o <;> simp [Clause.eval]

private theorem branch_unit (φ : CNF) (n : ℕ) : IsKCNF 1 (branch φ n) := by
  induction φ generalizing n with
  | nil => simp [branch, IsKCNF]
  | cons c cs ih =>
      intro d h
      simp only [branch, List.mem_cons] at h
      rcases h with rfl | h
      · cases getElem? c (n % c.length) <;> simp
      · exact ih _ d h

private theorem branch_sound (φ : CNF) (n : ℕ) (σ : Assignment)
    (h : (branch φ n).eval σ = true) : φ.eval σ = true := by
  induction φ generalizing n with
  | nil => rfl
  | cons c cs ih =>
      simp only [branch, CNF.eval, List.all_cons, Bool.and_eq_true] at h ⊢
      obtain ⟨l,hl,ht⟩ := (unit_sat _ σ).mp h.1
      exact ⟨List.any_eq_true.mpr ⟨l,List.mem_of_getElem? hl,ht⟩, ih _ h.2⟩

private theorem branch_complete (φ : CNF) (σ : Assignment) (h : φ.eval σ = true) :
    ∃ n < (φ.map List.length).prod, (branch φ n).eval σ = true := by
  induction φ with
  | nil => exact ⟨0, by decide, rfl⟩
  | cons c cs ih =>
      simp only [CNF.eval, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨l,hl,ht⟩ := List.any_eq_true.mp h.1
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hl
      have hil : i < c.length := by
        by_contra hn
        have hnone : c[i]? = none := List.getElem?_eq_none (by omega)
        rw [hnone] at hi
        simp at hi
      obtain ⟨j,hj,htrue⟩ := ih h.2
      have hc : 0 < c.length := by omega
      refine ⟨i+c.length*j, ?_, ?_⟩
      · simp only [List.map_cons, List.prod_cons]
        have h1 : i + c.length*j < c.length*(j+1) := by rw [Nat.mul_succ]; omega
        exact h1.trans_le (Nat.mul_le_mul_left _ (by omega))
      · simp only [branch, CNF.eval, List.all_cons, Bool.and_eq_true]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hil, Nat.add_mul_div_left _ _ hc,
          Nat.div_eq_of_lt hil, Nat.zero_add]
        exact ⟨(unit_sat _ σ).mpr ⟨l,hi,ht⟩, htrue⟩

/-- Measured mixed-radix branching produces unit clauses. Every satisfying assignment
chooses a compatible branch with index below the product of original clause widths. -/
theorem MeasuredMixedRadixUnits :
    ∃ choose : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) choose ∧
      (∀ (φ : CNF) (ix : List Bool), ∃ units : CNF, IsKCNF 1 units ∧
        choose (ix, encodeCNF φ) = encodeCNF units ∧
        ∀ σ : Assignment, units.eval σ = true → φ.eval σ = true) ∧
      ∀ (φ : CNF) (σ : Assignment), φ.eval σ = true →
        ∃ i < (φ.map List.length).prod, ∃ units : CNF,
          choose (List.replicate i true, encodeCNF φ) = encodeCNF units ∧ units.eval σ = true := by
  obtain ⟨split,hs,hjoin,hspec⟩ := measuredFirstClause_reassembles
  obtain ⟨count,hc,hcspec⟩ := MeasuredClauseLiteralCount
  obtain ⟨divide,hd,hdspec⟩ := MeasuredUnaryDivMod
  obtain ⟨pick,hp,hpspec⟩ := MeasuredLiteralChoice
  let loop := fun s => (step split count divide pick)^[(unpairB s).2.length]
    (pairB (unpairB s).2 (pairB (unpairB s).1 []))
  let choose := fun p : List Bool × List Bool => (unpairB (unpairB (loop (pairB p.1 p.2))).2).2
  have hloop : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) loop :=
    cpt_iterGrow (step_cpt hs hc hd hp) 2 (step_length hjoin hdspec) cpt_unpairB2
      (cpt_pairB2 cpt_unpairB2 (cpt_pairB2 cpt_unpairB1 (cpt_const [])))
  have hchoose : ComputableInPolyTime encodePair (fun x : List Bool => x) choose :=
    cpt_comp (g := fun s => (unpairB (unpairB (loop s)).2).2) cpt_pairB
      (cpt_unpairB2_1 (cpt_unpairB2_1 hloop))
  have hsem (φ : CNF) (ix : List Bool) : choose (ix,encodeCNF φ) = encodeCNF (branch φ ix.length) := by
    simp only [choose, loop, unpairB_pairB]
    rw [run hspec hcspec hdspec hpspec _ _ _ _ (formula_length φ), List.nil_append]
  refine ⟨choose,hchoose,?_,?_⟩
  · intro φ ix
    exact ⟨_,branch_unit φ ix.length,hsem φ ix,fun σ => branch_sound φ ix.length σ⟩
  · intro φ σ ht
    obtain ⟨i,hi,hb⟩ := branch_complete φ σ ht
    exact ⟨i,hi,branch φ i,by simpa using hsem φ (List.replicate i true),hb⟩

end PEqualNP.Outside
