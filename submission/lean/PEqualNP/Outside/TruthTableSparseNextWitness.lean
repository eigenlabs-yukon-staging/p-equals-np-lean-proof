import PEqualNP.Outside.LexTruthTableSparseWitness

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)
local notation "ltBit" => (fun x y : Bool => !x && y)

private def afterCursor (cursor witness : Word) : Bool :=
  cursor.isEmpty || cursor.tail.lex witness ltBit

private def testLater (v : Word × Word → Bool) (p : Word × Word) : Bool :=
  let tag := unpairB p.1
  v (tag.1,p.2) && afterCursor tag.2 p.2

private theorem testLater_cpt {v : Word × Word → Bool}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair Computability.encodeBool (testLater v) := by
  have hinput := cpt_unpairB1_1 cpt_unpairB1
  have hcursor := cpt_unpairB2_1 cpt_unpairB1
  have hcmp := cpt_bitFlag (cpt_comp (cpt_pair (cpt_comp hcursor cpt_tail) cpt_unpairB2)
    LexicographicWordCompare)
  have hchoice := cpt_sel hcursor (cpt_const [true]) hcmp
  have hvalid := cpt_bitFlag (cpt_comp (cpt_pair hinput cpt_unpairB2) hv)
  have h := cpt_comp (cpt_sel hchoice (cpt_const []) hvalid) bf_cpt_neL
  apply cpt_fromRawBool (f := testLater v)
  refine bf_cptl h ?_
  intro s
  let p := unpairB s
  let tag := unpairB p.1
  let a := tag.2.tail.lex p.2 ltBit
  let b := v (tag.1,p.2)
  change (!(sel (sel tag.2 [true] (bflag a)) [] (bflag b)).isEmpty) =
      (b && (tag.2.isEmpty || a))
  cases tag.2 <;> cases a <;> cases b <;> rfl

private theorem afterCursor_spec (cursor witness : Word) :
    afterCursor cursor witness = true ↔ cursor = [] ∨ cursor.tail < witness := by
  have e : ltBit = (fun x y : Bool => decide (x < y)) := by
    funext x y
    cases x <;> cases y <;> rfl
  simp [afterCursor,e,List.lex_eq_true_iff_lt]

/-- The measured successor for a tagged witness cursor. Empty cursor requests the
first answer. A nonempty cursor requests the least witness strictly after its tail. -/
theorem TruthTableSparseNextWitness (R : Set (Word × Word))
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
    ∃ next : Word × Word → Word,
      ComputableInPolyTime encodePair (fun x => x) next ∧ ∀ x cursor : Word,
        (next (x,cursor) = [] ∧ ∀ w : Word, (x,w) ∈ R →
          ¬(cursor = [] ∨ cursor.tail < w)) ∨
        ∃ w : Word, next (x,cursor) = true :: w ∧ (x,w) ∈ R ∧
          (cursor = [] ∨ cursor.tail < w) ∧
          ∀ u : Word, (x,u) ∈ R → (cursor = [] ∨ cursor.tail < u) → w ≤ u := by
  obtain ⟨v,hvSpec,hv⟩ := hR
  let E : Set (Word × Word) := {p | testLater v p = true}
  have hE : DecidableInPolyTime encodePair E := ⟨testLater v,fun _ => Iff.rfl,testLater_cpt hv⟩
  have hlen (y w : Word) (hy : (y,w) ∈ E) : w.length ≤ p.eval y.length := by
    change testLater v (y,w) = true at hy
    have h := (Bool.and_eq_true_iff.mp hy).1
    have hx := bound (unpairB y).1 w ((hvSpec _).mpr h)
    have he : (unpairB y).1.length ≤ y.length := by
      have := unpairB_length y
      omega
    exact hx.trans (eval_mono p he)
  have spec (x cursor w : Word) : (pairB x cursor,w) ∈ E ↔
      (x,w) ∈ R ∧ (cursor = [] ∨ cursor.tail < w) := by
    change testLater v (pairB x cursor,w) = true ↔ _
    simp only [testLater,unpairB_pairB,Bool.and_eq_true,← hvSpec,afterCursor_spec]
  obtain ⟨f,hf,hs⟩ := LexTruthTableSparseWitness E hE p hlen A B hA s sparse k q hq T hT relation
  refine ⟨(fun p => f (pairB p.1 p.2)),cpt_comp cpt_pairB hf,fun x cursor => ?_⟩
  rcases hs (pairB x cursor) with ⟨hn,hNo⟩ | ⟨w,hw,ha,hMin⟩
  · exact Or.inl ⟨hn,fun w hw he => hNo w ((spec x cursor w).mpr ⟨hw,he⟩)⟩
  · have h := (spec x cursor w).mp ha
    exact Or.inr ⟨w,hw,h.1,h.2,fun u hu he => hMin u ((spec x cursor u).mpr ⟨hu,he⟩)⟩

end PEqualNP.Outside
