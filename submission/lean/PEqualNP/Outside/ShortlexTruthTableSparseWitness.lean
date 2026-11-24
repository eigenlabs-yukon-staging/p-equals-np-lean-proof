import PEqualNP.Outside.VariableTruthTableSparseWitness
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import Mathlib.Data.List.Lex

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

def padShortlex (n : Nat) (w : Word) : Word :=
  pairB w (un (2*(n-w.length)))

theorem padShortlex_length (n : Nat) (w : Word) (hw : w.length ≤ n) :
    (padShortlex n w).length = 2*n + 1 := by
  simp [padShortlex, pairB_length, un_length]
  omega

theorem padShortlex_order (n : Nat) (u w : Word)
    (h : u.length < w.length ∨ u.length = w.length ∧ u < w) :
    padShortlex n u < padShortlex n w := by
  rcases h with shorter | ⟨same,lex⟩
  · obtain ⟨d,he⟩ : ∃ d : Nat, w.length = u.length + (d+1) := ⟨w.length - u.length - 1, by omega⟩
    unfold padShortlex pairB
    simp only [un]
    conv_rhs => rw [he, ← List.replicate_append_replicate, List.append_assoc]
    apply (List.append_left_lt_iff _).mpr
    rw [List.replicate_succ, List.cons_append]
    exact List.cons_lt_cons_iff.mpr (Or.inl (by decide))
  · unfold padShortlex pairB
    simp only [un]
    rw [← same]
    apply (List.append_left_lt_iff _).mpr
    apply List.cons_lt_cons_iff.mpr
    refine Or.inr ⟨rfl, ?_⟩
    exact (List.append_lt_append_iff_of_length_eq same).mpr (Or.inl lex)

private theorem tailIter (k : Nat) (x : Word) : (fun w : Word => w.tail)^[k] x = x.drop k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases x <;> simp

theorem padShortlex_cpt (p : Polynomial Nat) :
    ComputableInPolyTime encodePair (fun x => x)
      (fun q : Word × Word => padShortlex (p.eval q.1.length) q.2) := by
  let n := fun s : Word => un (p.eval (unpairB s).1.length)
  have hn : CPT n := cpt_comp (g := fun w : Word => un (p.eval w.length)) cpt_unpairB1 (L055 p)
  let rest := fun s : Word => (n s).drop (unpairB s).2.length
  have hr : CPT rest := bf_cptl
    (cpt_iterLen cpt_tail (fun w => by simp) cpt_unpairB2 hn)
    (fun s => by simp [tailIter,rest])
  have hc := cpt_pairB2 cpt_unpairB2 (cpt_app2 hr hr)
  apply cpt_fromRaw
  refine bf_cptl hc ?_
  intro s
  simp [padShortlex, rest, n, un, Nat.two_mul]

private def canonicalCheck (normalize : Word × Word → Word) (decode : Word → Word)
    (v : Word × Word → Bool) (q : Word × Word) : Bool :=
  let w := decode q.2
  decide (q.2 = normalize (q.1,w)) && v (q.1,w)

private theorem canonicalCheck_cpt {normalize : Word × Word → Word} {decode : Word → Word}
    {v : Word × Word → Bool}
    (hn : ComputableInPolyTime encodePair (fun x => x) normalize) (hd : CPT decode)
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair Computability.encodeBool (canonicalCheck normalize decode v) := by
  have hw := cpt_comp cpt_unpairB2 hd
  have harg := cpt_pair cpt_unpairB1 hw
  have hp := cpt_comp harg hn
  have he := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF cpt_unpairB2 hp
  have hv' := cpt_bitFlag (cpt_comp harg hv)
  have hc := cpt_comp (cpt_sel he (cpt_const []) hv') bf_cpt_neL
  apply cpt_fromRawBool (f := canonicalCheck normalize decode v)
  refine bf_cptl hc ?_
  intro s
  let w := decode (unpairB s).2
  let a := decide ((unpairB s).2 = normalize ((unpairB s).1,w))
  let b := v ((unpairB s).1,w)
  change (!(sel (bflag a) [] (bflag b)).isEmpty) = (a && b)
  cases a <;> cases b <;> rfl

theorem measuredCanonicalPadding (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R)
    (normal : Word × Word → Word)
    (hNormal : ComputableInPolyTime encodePair (fun x => x) normal)
    (decode : Word → Word) (hDecode : CPT decode)
    (inverse : ∀ (x w : Word), decode (normal (x,w)) = w) :
    ∃ E : Set (Word × Word), DecidableInPolyTime encodePair E ∧
      (∀ x z : Word, (x,z) ∈ E ↔ ∃ w : Word, (x,w) ∈ R ∧ z = normal (x,w)) := by
  obtain ⟨v,hs,hv⟩ := hR
  let test := canonicalCheck normal decode v
  refine ⟨{q | test q = true},⟨test,fun _ => Iff.rfl,canonicalCheck_cpt hNormal hDecode hv⟩,?_⟩
  intro x z
  change test (x,z) = true ↔ _
  constructor
  · intro h
    have e := Bool.and_eq_true_iff.mp h
    exact ⟨decode z, (hs _).mpr e.2, of_decide_eq_true e.1⟩
  · rintro ⟨w,hw,rfl⟩
    simp [test,canonicalCheck,inverse,(hs _).mp hw]

/-- Canonical unary-length padding preserves the order by length, then lexicographically,
and supplies a measured exact-length verifier for every polynomially bounded relation. -/
theorem ShortlexWitnessPadding (R : Set (Word × Word))
    (hR : DecidableInPolyTime encodePair R) (p : Polynomial Nat)
    (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length) :
    ∃ E : Set (Word × Word),
      DecidableInPolyTime encodePair E ∧
      (∀ x z : Word, (x,z) ∈ E ↔ ∃ w : Word, (x,w) ∈ R ∧
        z = padShortlex (p.eval x.length) w) ∧
      (∀ x z : Word, (x,z) ∈ E → z.length = (Polynomial.C 2*p+1).eval x.length) := by
  obtain ⟨E,hE,hs⟩ := measuredCanonicalPadding R hR
    (fun q => padShortlex (p.eval q.1.length) q.2) (padShortlex_cpt p)
    (fun w => (unpairB w).1) cpt_unpairB1 (fun x w => by simp [padShortlex,unpairB_pairB])
  refine ⟨E,hE,hs,fun x z hz => ?_⟩
  obtain ⟨w,hw,rfl⟩ := (hs x z).mp hz
  simpa using padShortlex_length (p.eval x.length) w (bound x w hw)

private def stripPadding (s : Word) : Word :=
  sel s [] (true :: (unpairB s.tail).1)

private theorem stripPadding_cpt : CPT stripPadding :=
  cpt_sel cpt_id (cpt_const []) (cpt_cons1 true (cpt_unpairB1_1 cpt_tail))

/-- Returns an accepted witness of minimum length, breaking ties by the ordinary
Boolean-word lexicographic order, under the bounded sparse reduction hypothesis. -/
theorem ShortlexTruthTableSparseWitness (R : Set (Word × Word))
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
    ∃ f : Word → Word, CPT f ∧ ∀ x : Word,
      (f x = [] ∧ ∀ w : Word, (x,w) ∉ R) ∨
        ∃ w : Word, f x = true :: w ∧ (x,w) ∈ R ∧
          ∀ u : Word, (x,u) ∈ R → w.length ≤ u.length ∧ (w.length = u.length → w ≤ u) := by
  obtain ⟨E,hE,hESpec,hLen⟩ := ShortlexWitnessPadding R hR p bound
  obtain ⟨run,hr,hs⟩ :=
    VariableTruthTableSparseWitness E hE (Polynomial.C 2*p+1) hLen A B hA s sparse k q hq T hT relation
  refine ⟨fun x => stripPadding (run x),cpt_comp hr stripPadding_cpt,fun x => ?_⟩
  rcases hs x with ⟨hn,hNo⟩ | ⟨z,hz,ha,hMin⟩
  · refine Or.inl ⟨by simp [hn,stripPadding], fun w hw => ?_⟩
    exact hNo _ ((hESpec _ _).mpr ⟨w,hw,rfl⟩)
  · obtain ⟨w,hw,rfl⟩ := (hESpec _ _).mp ha
    have horder (u : Word) (hu : (x,u) ∈ R) :
        ¬(u.length < w.length ∨ u.length = w.length ∧ u < w) := by
      intro h
      have hc := (hESpec x (padShortlex (p.eval x.length) u)).mpr ⟨u,hu,rfl⟩
      exact not_lt_of_ge (hMin _ hc) (padShortlex_order (p.eval x.length) u w h)
    refine Or.inr ⟨w,by simp [hz,stripPadding,padShortlex,unpairB_pairB,sel],hw,fun u hu => ?_⟩
    exact ⟨le_of_not_gt (fun h => horder u hu (Or.inl h)),
      fun he => le_of_not_gt (fun h => horder u hu (Or.inr ⟨he.symm,h⟩))⟩

end PEqualNP.Outside
