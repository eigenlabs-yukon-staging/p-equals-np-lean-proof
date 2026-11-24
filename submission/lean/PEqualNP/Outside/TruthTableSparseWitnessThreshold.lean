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

private theorem enough_iff (R : Set (Word × Word)) (x : Word) (xs : List Word) (n : Nat)
    (sorted : xs.Pairwise (· < ·)) (full : ∀ w : Word, w ∈ xs ↔ (x,w) ∈ R) :
    n ≤ xs.length ↔ ∃ S : Finset Word, S.card = n ∧ ∀ w ∈ S, (x,w) ∈ R := by
  have hnd : xs.Nodup := sorted.imp (fun h => ne_of_lt h)
  constructor
  · intro enough
    let ys := xs.take n
    have sy : ys.Sublist xs := List.take_sublist _ _
    have hlen : ys.length = n := by simp [ys,Nat.min_eq_left enough]
    refine ⟨ys.toFinset,(List.toFinset_card_of_nodup (hnd.sublist sy)).trans hlen,fun w hw => ?_⟩
    exact (full w).mp (sy.subset (List.mem_toFinset.mp hw))
  · rintro ⟨S,hc,hs⟩
    have ss : S ⊆ xs.toFinset := fun w hw => List.mem_toFinset.mpr ((full w).mpr (hs w hw))
    simpa [hc,List.toFinset_card_of_nodup hnd] using Finset.card_le_card ss

/-- Under the bounded sparse reduction hypothesis, the unary threshold for the
number of distinct accepted witnesses is decidable by a pinned polynomial-time machine. -/
theorem TruthTableSparseWitnessThreshold (R : Set (Word × Word))
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
    ∃ test : Word × Word → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧ ∀ x fuel : Word,
        test (x,fuel) = true ↔
          ∃ S : Finset Word, S.card = fuel.length ∧ ∀ w ∈ S, (x,w) ∈ R := by
  obtain ⟨run,hr,hlist,hs⟩ :=
    TruthTableSparseWitnessEnumeration R hR p bound A B hA s sparse k q hq T hT relation
  let test := fun q : Word × Word => decide (q.2.length ≤ (countPacked (run q)).length)
  have ht : ComputableInPolyTime encodePair Computability.encodeBool test := by
    have h := cpt_comp (cpt_pair (cpt_comp (cpt_comp cpt_unpairB hr) countPacked_cpt) cpt_unpairB2)
      LenCmp.lenLE_polyTime
    exact cpt_fromRawBool (f := test) h
  refine ⟨test,ht,fun x fuel => ?_⟩
  obtain ⟨xs,sorted,full⟩ := hlist x
  have e : run (x,fuel) = encodeFrontier (xs.take fuel.length) := hs x fuel xs sorted full
  change decide (fuel.length ≤ (countPacked (run (x,fuel))).length) = true ↔ _
  rw [e,countPacked_length,List.length_take,decide_eq_true_eq]
  simpa only [Nat.le_min, le_refl, true_and] using enough_iff R x xs fuel.length sorted full

end PEqualNP.Outside
