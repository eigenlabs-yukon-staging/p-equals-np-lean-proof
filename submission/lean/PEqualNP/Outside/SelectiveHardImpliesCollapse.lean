import PEqualNP.Outside.SparseHardImpliesCollapse
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open SparseFrontierSupport

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Picker" => Word × Word → Word
local notation "Verifier" => Word × Word → Bool

private def Selects (A : Language Bool) (s : Picker) : Prop :=
  ∀ x y : Word, (s (x,y) = x ∨ s (x,y) = y) ∧
    (x ∈ A ∨ y ∈ A → s (x,y) ∈ A)

private def pullSelector (reduce : Word → Word) (choose : Picker) (p : Word × Word) : Word :=
  if choose (reduce p.1, reduce p.2) = reduce p.1 then p.1 else p.2

private theorem pullSelector_polyTime {reduce : Word → Word} {choose : Picker}
    (hr : CPT reduce) (hc : ComputableInPolyTime encodePair (fun x => x) choose) :
    ComputableInPolyTime encodePair (fun x => x) (pullSelector reduce choose) := by
  have hx := cpt_comp cpt_unpairB1 hr
  have hy := cpt_comp cpt_unpairB2 hr
  have hc' := cpt_comp (cpt_pair hx hy) hc
  have eq := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF hc' hx
  have hf := cpt_comp cpt_pairB (cpt_sel eq cpt_unpairB2 cpt_unpairB1)
  apply bf_cptl hf
  rintro ⟨x,y⟩
  by_cases he : choose (reduce x, reduce y) = reduce x <;>
    simp [pullSelector, unpairB_pairB, bflag, he]

private theorem pullSelector_spec (A B : Language Bool) (reduce : Word → Word) (choose : Picker)
    (hr : ∀ x, x ∈ A ↔ reduce x ∈ B) (hc : Selects B choose) :
    Selects A (pullSelector reduce choose) := by
  intro x y
  have h := hc (reduce x) (reduce y)
  by_cases he : choose (reduce x, reduce y) = reduce x
  · simp only [pullSelector, he, ite_true, true_or, true_and]
    intro hs
    have hz := h.2 (hs.elim (fun hx => Or.inl ((hr x).mp hx)) (fun hy => Or.inr ((hr y).mp hy)))
    exact (hr x).mpr (he ▸ hz)
  · simp only [pullSelector, he, ite_false, or_true, true_and]
    intro hs
    have hz := h.2 (hs.elim (fun hx => Or.inl ((hr x).mp hx)) (fun hy => Or.inr ((hr y).mp hy)))
    exact (hr y).mpr ((h.1.resolve_left he) ▸ hz)

private def selectStep (v : Verifier) (choose : Picker) (s : Word) : Word :=
  let x := (unpairB s).1
  let w := (unpairB s).2
  sel (bflag (v (x,w)))
    (choose (pairB x (w ++ [false]), pairB x (w ++ [true]))) s

private theorem selectStep_length {v : Verifier} {choose : Picker}
    (h : Selects (prefixExtension v) choose) (s : Word) :
    (selectStep v choose s).length ≤ s.length + 2 := by
  have hs := unpairB_length s
  unfold selectStep
  dsimp only
  apply sel_length
  · rcases (h (pairB (unpairB s).1 ((unpairB s).2 ++ [false]))
      (pairB (unpairB s).1 ((unpairB s).2 ++ [true]))).1 with h₀ | h₁
    · rw [h₀, pairB_length, List.length_append]; simp; omega
    · rw [h₁, pairB_length, List.length_append]; simp; omega
  · omega

private theorem selectStep_polyTime {v : Verifier} {choose : Picker}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (hc : ComputableInPolyTime encodePair (fun x => x) choose) : CPT (selectStep v choose) := by
  have h₀ := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [false]))
  have h₁ := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [true]))
  have hstop := cpt_bitFlag (cpt_comp cpt_unpairB hv)
  exact bf_cptl (cpt_sel hstop (cpt_comp (cpt_pair h₀ h₁) hc) cpt_id) (fun _ => rfl)

private theorem selectStep_child (v : Verifier) (choose : Picker)
    (h : Selects (prefixExtension v) choose) (x w : Word) :
    selectStep v choose (pairB x w) ∈ children v (pairB x w) := by
  cases hv : v (x,w)
  · have he := (h (pairB x (w ++ [false])) (pairB x (w ++ [true]))).1
    simp [selectStep, children, unpairB_pairB, bflag, hv, he]
  · simp [selectStep, children, unpairB_pairB, bflag, hv]

private theorem selectStep_accept (v : Verifier) (choose : Picker)
    (h : Selects (prefixExtension v) choose) (x w : Word)
    (hw : pairB x w ∈ prefixExtension v) :
    selectStep v choose (pairB x w) ∈ prefixExtension v := by
  cases hv : v (x,w)
  · obtain ⟨z, hm, hz⟩ := (child_extension v x w).mpr hw
    have e : z = pairB x (w ++ [false]) ∨ z = pairB x (w ++ [true]) := by
      simpa [children, unpairB_pairB, hv] using hm
    have hm : pairB x (w ++ [false]) ∈ prefixExtension v ∨
        pairB x (w ++ [true]) ∈ prefixExtension v :=
      e.elim (fun h => Or.inl (h ▸ hz)) (fun h => Or.inr (h ▸ hz))
    simpa [selectStep, unpairB_pairB, hv, bflag] using
      (h (pairB x (w ++ [false])) (pairB x (w ++ [true]))).2 hm
  · simpa [selectStep, unpairB_pairB, hv, bflag] using hw

private theorem selectRun (v : Verifier) (choose : Picker) (h : Selects (prefixExtension v) choose)
    (x : Word) (n : Nat) :
    let s := (selectStep v choose)^[n] (pairB x [])
    atDepth v x n s ∧ (pairB x [] ∈ prefixExtension v → s ∈ prefixExtension v) := by
  induction n with
  | zero => exact ⟨⟨[], rfl, le_rfl, Or.inr rfl⟩, id⟩
  | succ n ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    obtain ⟨⟨w, hw, hlen, hfin⟩, he⟩ := ih
    have hchild := selectStep_child v choose h x w
    rw [hw]
    exact ⟨children_depth v x n (⟨w, rfl, hlen, hfin⟩ : atDepth v x n (pairB x w)) hchild,
      fun hinit => selectStep_accept v choose h x w (hw ▸ he hinit)⟩

private theorem decideSelected {v : Verifier} {choose : Picker}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (hc : ComputableInPolyTime encodePair (fun x => x) choose)
    (h : Selects (prefixExtension v) choose) (p : Polynomial Nat)
    (hb : ∀ x w : Word, v (x,w) = true → w.length ≤ p.eval x.length) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  let run := fun x : Word => (selectStep v choose)^[p.eval x.length] (pairB x [])
  have hr : CPT run :=
    bf_cptl (cpt_iterGrow (selectStep_polyTime hv hc) 2 (selectStep_length h) (L055 p)
      (cpt_pairB2 cpt_id (cpt_const []))) (fun x => by simp [run])
  let f := fun x : Word => v (unpairB (run x))
  have hf : ComputableInPolyTime (fun x => x) Computability.encodeBool f :=
    cpt_comp (cpt_comp hr cpt_unpairB) hv
  refine ⟨f, fun x => ?_, hf⟩
  obtain ⟨⟨w, hstate, _, hfin⟩, he⟩ := selectRun v choose h x (p.eval x.length)
  change run x = pairB x w at hstate
  change (∃ w : Word, v (x,w) = true) ↔ v (unpairB (run x)) = true
  rw [hstate, unpairB_pairB]
  constructor
  · intro hex
    rcases hfin with hyes | hlen
    · exact hyes
    · have hmem : pairB x [] ∈ prefixExtension v := by
        simpa using (prefixExtension_pair v x []).mpr (by simpa using hex)
      have hout := he hmem
      change run x ∈ prefixExtension v at hout
      rw [hstate] at hout
      obtain ⟨t, ht⟩ := (prefixExtension_pair v x w).mp hout
      have hn := hb x (w ++ t) ht
      have hnil : t = [] := List.length_eq_zero_iff.mp (by rw [List.length_append] at hn; omega)
      simpa [hnil] using ht
  · exact fun h => ⟨w,h⟩

/-- A polynomial-time selector for any pinned NP-hard language implies collapse. -/
theorem SelectiveHardImpliesCollapse (B : Language Bool) (hB : NPHard B)
    (choose : Picker) (hc : ComputableInPolyTime encodePair (fun x => x) choose)
    (hs : ∀ x y : Word, (choose (x,y) = x ∨ choose (x,y) = y) ∧
      (x ∈ B ∨ y ∈ B → choose (x,y) ∈ B)) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro A hA
  obtain ⟨R, p, ⟨v, spec, hv⟩, bound, heq⟩ := L045 A hA
  have hb (x w : Word) (h : v (x,w) = true) : w.length ≤ p.eval x.length :=
    bound x w ((spec (x,w)).mpr h)
  obtain ⟨reduce, hr, hspec⟩ := hB _ (prefixExtension_np hv p hb)
  have hs' := pullSelector_spec _ _ reduce choose hspec hs
  have e : A = ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) :=
    Set.ext (fun x => (heq x).trans (exists_congr (fun w => spec (x,w))))
  rw [e]
  exact decideSelected hv (pullSelector_polyTime hr hc) hs' p hb

end PEqualNP.Outside
