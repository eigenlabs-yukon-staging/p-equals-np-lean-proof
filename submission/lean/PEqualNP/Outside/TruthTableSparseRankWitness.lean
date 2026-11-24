import PEqualNP.Outside.TruthTableSparseWitnessEnumeration

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

private noncomputable def countPacked (s : Word) : Word :=
  expandFrontier (fun _ => [false]) 1 s

private theorem countPacked_cpt : CPT countPacked := expandFrontier_polyTime (cpt_const [false]) 1

private theorem countPacked_length (xs : List Word) :
    (countPacked (encodeFrontier xs)).length = xs.length := by
  have spec := expandFrontier_spec
    (fun _ => ([[]] : List Word)) (fun _ => [false]) (fun _ => rfl) 1 (by simp) xs
  change countPacked (encodeFrontier xs) = _ at spec
  rw [spec]
  clear spec
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (pairB [] (encodeFrontier (xs.flatMap (fun _ => [[]])))).length = xs.length + 1
    simp only [pairB_length,List.length_nil,Nat.mul_zero,Nat.zero_add,ih]

/-- Select the zero-based unary rank of an accepted witness under the measured
bounded sparse reduction hypothesis, with an explicit out-of-range result. -/
theorem TruthTableSparseRankWitness (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (hq : ∀ i, CPT (fun x => q x i))
    (T : Word → (Fin k → Bool) → Bool)
    (hT : ∀ a, ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun x => T x a))
    (relation : ∀ x : Word, x ∈ A ↔
      T x (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)) = true) :
    ∃ select : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) select ∧
      ∀ (x fuel : Word) (ws : List Word), ws.Pairwise (· < ·) →
        (∀ w : Word, w ∈ ws ↔ (x,w) ∈ R) →
        select (x,fuel) = (ws[fuel.length]?.map (List.cons true)).getD [] := by
  obtain ⟨enum,henum,_,hs⟩ :=
    TruthTableSparseWitnessEnumeration R hR p bound A B hA s sparse k q hq T hT relation
  have htrue : ComputableInPolyTime encodePair Computability.encodeBool (fun _ : Word × Word => true) := by
    have h := cpt_comp cpt_pairB (cpt_comp (cpt_const [true]) bf_cpt_neL)
    exact bf_cptl h (fun _ => rfl)
  obtain ⟨last,hlast,hsLast⟩ := LastEncodedMatch (fun _ => true) htrue
  let raw := fun w : Word =>
    let p := unpairB w
    let fuel := true :: p.2
    let out := enum (p.1,fuel)
    sel (bflag (decide (fuel.length ≤ (countPacked out).length))) [] (last ([],out))
  have hc : CPT raw := by
    have hfuel := cpt_cons1 true cpt_unpairB2
    have hout := cpt_comp (cpt_pair cpt_unpairB1 hfuel) henum
    have hflag := cpt_bitFlag (cpt_comp (cpt_pair (cpt_comp hout countPacked_cpt) hfuel)
      LenCmp.lenLE_polyTime)
    exact cpt_sel hflag (cpt_const []) (cpt_comp (cpt_pair (cpt_const []) hout) hlast)
  let select := fun p : Word × Word => raw (pairB p.1 p.2)
  refine ⟨select,cpt_comp cpt_pairB hc,fun x fuel ws sorted full => ?_⟩
  let ys := ws.take (fuel.length+1)
  have he : enum (x,true::fuel) = encodeFrontier ys := hs x (true::fuel) ws sorted full
  have hl : last ([],encodeFrontier ys) = (ys.getLast?.map (List.cons true)).getD [] := by
    have h := hsLast [] ys
    change last ([],encodeFrontier ys) = ((ys.filter (fun _ => true)).getLast?.map (List.cons true)).getD [] at h
    simpa using h
  unfold select raw
  simp only [unpairB_pairB,he,countPacked_length,List.length_cons,hl]
  by_cases h : fuel.length < ws.length
  · have enough : fuel.length + 1 ≤ ys.length := by simp [ys]; omega
    have e : ys.getLast? = ws[fuel.length]? := by
      rw [List.getElem?_eq_getElem h]
      change (ws.take (fuel.length+1)).getLast? = _
      rw [List.take_succ_eq_append_getElem h]
      exact List.getLast?_append_cons _ _ []
    simp [bflag,enough,sel,e]
  · have no : ¬ fuel.length + 1 ≤ ys.length := by simp [ys]; omega
    have hn : ws[fuel.length]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [bflag,no,sel,hn]

end PEqualNP.Outside
