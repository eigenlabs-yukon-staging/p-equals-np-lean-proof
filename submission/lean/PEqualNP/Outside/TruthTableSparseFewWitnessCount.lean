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

/-- With a polynomial cardinality bound, the sparse-reduction hypothesis
gives the exact count of all accepted witnesses as a measured unary word. -/
theorem TruthTableSparseFewWitnessCount (R : Set (Word × Word))
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
    ∀ (m : Polynomial Nat),
      (∀ (x : Word) (S : Finset Word), (∀ w ∈ S, (x,w) ∈ R) → S.card ≤ m.eval x.length) →
      ∃ count : Word → Word, CPT count ∧ ∀ (x : Word) (S : Finset Word),
        (∀ w : Word, w ∈ S ↔ (x,w) ∈ R) →
        count x = List.replicate S.card true := by
  intro m few
  obtain ⟨run,hr,hlist,hs⟩ :=
    TruthTableSparseWitnessEnumeration R hR p bound A B hA s sparse k q hq T hT relation
  let enum := fun x : Word => run (x,un (m.eval x.length))
  have he : CPT enum := by
    have h := cpt_comp (cpt_pair cpt_id (L055 m)) hr
    exact h
  let count := fun x : Word => un (countPacked (enum x)).length
  have hc : CPT count := by
    have h := cpt_comp (cpt_comp he countPacked_cpt) (L055 Polynomial.X)
    exact bf_cptl h (fun x => by simp [count,un])
  refine ⟨count,hc,fun x S hS => ?_⟩
  obtain ⟨xs,sorted,full⟩ := hlist x
  have hnd : xs.Nodup := sorted.imp (fun h => ne_of_lt h)
  have eq : xs.toFinset = S := by
    ext w
    exact (List.mem_toFinset.trans (full w)).trans (hS w).symm
  have len : xs.length = S.card := by rw [← List.toFinset_card_of_nodup hnd,eq]
  have width : xs.length ≤ m.eval x.length := by
    rw [len]
    exact few x S (fun w hw => (hS w).mp hw)
  have e : enum x = encodeFrontier xs := by
    have h := hs x (un (m.eval x.length)) xs sorted full
    change run (x,un (m.eval x.length)) =
      encodeFrontier (xs.take (un (m.eval x.length)).length) at h
    simpa only [enum,un_length,List.take_of_length_le width] using h
  simp [count,e,countPacked_length,len,un]

end PEqualNP.Outside
