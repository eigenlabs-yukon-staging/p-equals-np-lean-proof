import PEqualNP.Outside.VariableTruthTableSparseCollapse
import PEqualNP.Outside.LexicographicWordCompare

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private theorem fixedIter (f : Word → Word) (hf : CPT f) (i : Nat) : CPT (f^[i]) := by
  induction i with
  | zero => exact cpt_id
  | succ i ih =>
    have step : CPT (f^[i] ∘ f) := cpt_comp (f := f) (g := f^[i]) hf ih
    rwa [Function.iterate_succ]

private theorem dropPacked (i : Nat) (xs : List Word) :
    (fun s : Word => (unpairB s).2)^[i] (encodeFrontier xs) = encodeFrontier (xs.drop i) := by
  induction i generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      have h : (unpairB (encodeFrontier [])).2 = encodeFrontier [] := rfl
      rw [h, ih]
      simp
    | cons x xs =>
      change (fun s : Word => (unpairB s).2)^[n] (unpairB (pairB x (encodeFrontier xs))).2 = _
      rw [unpairB_pairB, ih]
      rfl

private theorem dropBits (i : Nat) (w : Word) :
    (fun x : Word => x.tail)^[i] w = w.drop i := by
  induction i generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases w <;> simp

private theorem coordinateFromEncoding (k : Nat) (queries : Word → Fin k → Word)
    (table : Word → Word)
    (h : CPT (fun x => pairB (encodeFrontier (List.ofFn (queries x))) (table x)))
    (i : Fin k) : CPT (fun x => queries x i) := by
  have hp := cpt_unpairB1_1 h
  have htail := fixedIter (fun s : Word => (unpairB s).2) cpt_unpairB2 i.val
  refine bf_cptl (cpt_unpairB1_1 (cpt_comp hp htail)) ?_
  intro x
  simp only [unpairB_pairB, dropPacked]
  have hi : i.val < (List.ofFn (queries x)).length := by simp
  rw [List.drop_eq_getElem_cons hi]
  change (unpairB (pairB _ _)).1 = _
  rw [unpairB_pairB]
  simp

private theorem tableBitFromEncoding (k : Nat) (queries : Word → Fin k → Word)
    (table : Word → Word)
    (h : CPT (fun x => pairB (encodeFrontier (List.ofFn (queries x))) (table x)))
    (n : Nat) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool
      (fun x => ((table x).drop n).headD false) := by
  have ht : CPT table :=
    bf_cptl (cpt_unpairB2_1 h) (fun x => by simp [unpairB_pairB])
  refine bf_cptl (cpt_comp (cpt_comp ht (fixedIter (fun w : Word => w.tail) cpt_tail n))
    wordHead_polyTime) ?_
  intro x
  rw [dropBits]

/-- An explicit single encoded machine outputting both the fixed-arity query vector
and the table bits supplies the measured hypotheses of the bounded truth-table theorem. -/
theorem EncodedTruthTableSparseCollapse (A B : Language Bool) (hA : NPHard A)
    (s : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word), (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ s.eval n)
    (k : Nat) (q : Word → Fin k → Word) (table : Word → Word) (index : (Fin k → Bool) → Nat)
    (hc : CPT (fun x =>
      let pack := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
      pack ((List.ofFn (q x)).foldr pack []) (table x)))
    (spec : ∀ x : Word, x ∈ A ↔
      ((table x).drop (index (fun i => @decide (q x i ∈ B) (Classical.propDecidable _)))).headD false = true) :
    P = NP := by
  let truth := fun x a => ((table x).drop (index a)).headD false
  exact VariableTruthTableSparseCollapse A B hA s sparse k q
    (coordinateFromEncoding k q table hc) truth
    (fun a => tableBitFromEncoding k q table hc (index a)) spec

end PEqualNP.Outside
