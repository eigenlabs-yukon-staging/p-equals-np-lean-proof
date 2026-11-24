import PEqualNP.Outside.ThresholdWitnessNP
import PEqualNP.Library.L031
import PEqualNP.Library.L041

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool

private def amplifiedCheck (v : Word × Word → Bool) (q : Word × Word) : Bool :=
  let (x, budget) := unpairB q.1
  let (w, tag) := unpairB q.2
  decide (q.2 = pairB w tag) &&
    decide (tag = un tag.length) &&
    decide (tag.length < budget.length) &&
    v (x,w)

private theorem amplifiedCheck_cpt {v : Word × Word → Bool}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair Computability.encodeBool (amplifiedCheck v) := by
  let eqCpt := @PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF
  have hx := cpt_unpairB1_1 cpt_unpairB1
  have hb := cpt_unpairB2_1 cpt_unpairB1
  have hw := cpt_unpairB1_1 cpt_unpairB2
  have ht := cpt_unpairB2_1 cpt_unpairB2
  have hlen := cpt_bitFlag (cpt_comp (cpt_pair hb (cpt_cons1 true ht)) LenCmp.lenLE_polyTime)
  have htag := cpt_comp ht (L055 Polynomial.X)
  have htag' : ComputableInPolyTime (fun x : Word => x) (fun x => x)
      (fun s => un ((unpairB (unpairB s).2).2.length)) :=
    bf_cptl htag (fun s => by simp [un])
  have htagEq := eqCpt ht htag'
  have hcanonical := eqCpt cpt_unpairB2 (cpt_pairB2 hw ht)
  have hverify := cpt_bitFlag (cpt_comp (cpt_pair hx hw) hv)
  have h := cpt_comp (cpt_sel hcanonical (cpt_const [])
    (cpt_sel htagEq (cpt_const []) (cpt_sel hlen (cpt_const []) hverify))) bf_cpt_neL
  apply cpt_fromRawBool (f := amplifiedCheck v)
  refine bf_cptl h (fun s => ?_)
  let a := unpairB (unpairB s).1
  let b := unpairB (unpairB s).2
  let c : Bool := decide ((unpairB s).2 = pairB b.1 b.2)
  let d : Bool := decide (b.2 = un b.2.length)
  let e : Bool := decide (b.2.length + 1 ≤ a.2.length)
  let f : Bool := v (a.1,b.1)
  have he : e = decide (b.2.length < a.2.length) := rfl
  change (!(sel (bflag c) [] (sel (bflag d) [] (sel (bflag e) [] (bflag f)))).isEmpty) =
    (c && d && decide (b.2.length < a.2.length) && f)
  rw [← he]
  cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- There is one canonical amplified witness for every original accepted witness
and every unary tag index below the input budget. -/
theorem WitnessMultiplicityPadding (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length) :
    ∃ (E : Set (Word × Word)) (q : Polynomial Nat),
      DecidableInPolyTime encodePair E ∧
      (∀ y z : Word, (y,z) ∈ E → z.length ≤ q.eval y.length) ∧
      (∀ x fuel z : Word, (pairB x fuel,z) ∈ E ↔
        ∃ (w : Word) (i : Nat), (x,w) ∈ R ∧ i < fuel.length ∧ z = pairB w (un i)) := by
  obtain ⟨v,hvSpec,hv⟩ := hR
  let E : Set (Word × Word) := {q | amplifiedCheck v q = true}
  let q : Polynomial Nat := Polynomial.C 2 * p + Polynomial.X + 1
  refine ⟨E,q,⟨amplifiedCheck v,fun _ => Iff.rfl,amplifiedCheck_cpt hv⟩,fun y z hz => ?_,fun x fuel z => ?_⟩
  · change amplifiedCheck v (y,z) = true at hz
    simp only [amplifiedCheck,Bool.and_eq_true,decide_eq_true_eq] at hz
    obtain ⟨⟨⟨canonical, _⟩, tag⟩, hw⟩ := hz
    have h := unpairB_length y
    have hx : (unpairB y).1.length ≤ y.length := by omega
    have hp := (bound _ _ ((hvSpec _).mpr hw)).trans (eval_mono p hx)
    rw [canonical,pairB_length]
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega
  · change amplifiedCheck v (pairB x fuel,z) = true ↔ _
    simp only [amplifiedCheck,unpairB_pairB,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨canonical,tag⟩,hl⟩,hw⟩
      refine ⟨(unpairB z).1,(unpairB z).2.length,(hvSpec _).mpr hw,hl,?_⟩
      exact canonical.trans (congrArg (pairB (unpairB z).1) tag)
    · rintro ⟨w,i,hw,hi,rfl⟩
      simp [unpairB_pairB,(hvSpec _).mp hw,hi]

private theorem tag_injective (w : Word) : Function.Injective (fun i : Nat => pairB w (un i)) := by
  intro i j h
  have eq := congrArg (fun z : Word => (unpairB z).2.length) h
  simpa [unpairB_pairB] using eq

private theorem tag_witnesses (E : Set (Word × Word)) (R : Set (Word × Word))
    (spec : ∀ x fuel z : Word, (pairB x fuel,z) ∈ E ↔
      ∃ (w : Word) (i : Nat), (x,w) ∈ R ∧ i < fuel.length ∧ z = pairB w (un i))
    (x : Word) (k : Nat) (positive : 0 < k) :
    (∃ w : Word, (x,w) ∈ R) ↔
      ∃ S : Finset Word, S.card = k ∧ ∀ z ∈ S, (pairB x (un k),z) ∈ E := by
  constructor
  · rintro ⟨w,hw⟩
    let S := (Finset.range k).image (fun i => pairB w (un i))
    have hcard : S.card = k := by
      simp [S,Finset.card_image_of_injective _ (tag_injective w)]
    refine ⟨S,hcard,fun z hz => ?_⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact (spec x _ _).mpr ⟨w,i,hw,by simpa using Finset.mem_range.mp hi,rfl⟩
  · rintro ⟨S,hS,hs⟩
    have hne : S.Nonempty := Finset.card_pos.mp (hS.symm ▸ positive)
    obtain ⟨z,hz⟩ := hne
    obtain ⟨w,_,hw,_,_⟩ := (spec x _ _).mp (hs z hz)
    exact ⟨w,hw⟩

theorem witnessThresholdSlices (A : Language Bool) (hA : A ∈ NP) :
    ∃ L : Language Bool, L ∈ NP ∧
      ∀ k : Nat, 0 < k → ∀ x : Word,
        x ∈ A ↔ pairB (pairB x (un k)) (un k) ∈ L := by
  obtain ⟨R,p,hR,bound,hA'⟩ := L045 A hA
  obtain ⟨E,q,hE,hbound,he⟩ := WitnessMultiplicityPadding R hR p bound
  obtain ⟨L,hL,hs⟩ := ThresholdWitnessNP E hE q hbound
  refine ⟨L,hL,fun k positive x => ?_⟩
  have hh := hs (pairB x (un k)) (un k)
  change pairB (pairB x (un k)) (un k) ∈ L ↔ _ at hh
  rw [un_length] at hh
  exact (hA' x).trans ((tag_witnesses E R he x k positive).trans hh.symm)

/-- A single pinned NP-complete threshold language contains a measured SAT
reduction on each fixed positive unary request-count slice. -/
theorem ThresholdWitnessNPSlices :
    ∃ L : Language Bool, NPComplete L ∧
      ∀ k : Nat, 0 < k →
        ∃ reduce : Word → Word, ComputableInPolyTime (fun x => x) (fun x => x) reduce ∧
          ∀ x : Word,
            (let pack := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
             reduce x = pack (pack x (List.replicate k true)) (List.replicate k true)) ∧
            (x ∈ PEqualNP.Search.SAT ↔ reduce x ∈ L) := by
  obtain ⟨L,hL,hs⟩ := witnessThresholdSlices PEqualNP.Search.SAT L031.1
  have image (k : Nat) : ComputableInPolyTime (fun x : Word => x) (fun x => x)
      (fun x => pairB (pairB x (un k)) (un k)) :=
    cpt_pairB2 (cpt_pairB2 cpt_id (cpt_const (un k))) (cpt_const (un k))
  have reduced : PolyTimeReducible PEqualNP.Search.SAT L :=
    ⟨_,image 1,hs 1 (by decide)⟩
  refine ⟨L,⟨hL,L041 _ _ L031.2 reduced⟩,fun k h => ?_⟩
  exact ⟨_,image k,fun x => ⟨rfl,hs k h x⟩⟩

end PEqualNP.Outside
