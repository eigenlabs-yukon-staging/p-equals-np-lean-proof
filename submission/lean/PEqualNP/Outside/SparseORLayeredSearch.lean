import PEqualNP.Outside.SparseLayeredSearchMachine
import PEqualNP.Outside.QueryListAny
import PEqualNP.Library.Machines.ReduceNP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.SparseLayeredSearchMachine (expand run run_cpt run_invariant records pack)
open PEqualNP.Outside.QueryListAny (answer answer_cpt answer_enc)

theorem PEqualNP.Outside.SparseORLayeredSearch :
    ∀ (G A : Language Bool) (r : Polynomial ℕ),
      (∀ n : ℕ, ∃ S : Finset (List Bool), S.card ≤ r.eval n ∧
        ∀ y, y ∈ S ↔ y ∈ A ∧ y.length ≤ n) →
      (∃ f : List Bool × List Bool → List Bool,
        ComputableInPolyTime encodePair (fun w => w) f ∧
        ∀ x y, f (x,y) ∈ A ↔ x ∈ G ∨ y ∈ G) →
      ∀ (B : List Bool → List (List Bool)) (depth : Polynomial ℕ) (d : ℕ),
        (∀ x, x ∈ G ↔ ∃ y ∈ B x, y ∈ G) →
        (∀ x y, y ∈ B x → y.length ≤ x.length + d) →
        (∃ E : List (List Bool) → List Bool,
          E [] = [] ∧ (∀ a as, E (a :: as) = List.replicate a.length true ++ false :: (a ++ E as)) ∧
          ComputableInPolyTime (fun w => w) (fun w => w) (fun x => E (B x))) →
        (∃ test : List Bool → Bool,
          ComputableInPolyTime (fun w => w) Computability.encodeBool test ∧
          ∀ x y, y ∈ (fun l : List (List Bool) => l.flatMap B)^[depth.eval x.length] [x] →
            (test y = true ↔ y ∈ G)) →
        G ∈ P := by
  intro G A r hSparse ⟨f,hf,hred⟩ B depth d hB hg ⟨E,hE0,hEc,hEB⟩ ⟨test,hTest,hLeaf⟩
  have hE : ∀ rs, E rs = wire rs := by
    intro rs
    induction rs with
    | nil => exact hE0
    | cons a as ih => rw [hEc, ih]; rfl
  let branch (x : List Bool) := E (B x)
  have henc (x : List Bool) : branch x = wire (B x) := hE _
  obtain ⟨q,hq⟩ := output_length_poly (fun z => f (unpairB z)) (cpt_comp cpt_unpairB hf)
  let len : Polynomial ℕ := Polynomial.X + Polynomial.C d * depth
  let image : Polynomial ℕ := q.comp (3*len+1)
  let capPoly : Polynomial ℕ := r.comp image + 1
  let padPoly : Polynomial ℕ := capPoly * (2*len+1)
  let unary (p : Polynomial ℕ) (x : List Bool) := un (p.eval x.length)
  let out := run f branch (unary depth) (unary capPoly) (unary padPoly)
  have hout : ComputableInPolyTime (fun w => w) (fun w => w) out :=
    run_cpt f branch _ _ _ hf hEB (L055 depth) (L055 capPoly) (L055 padPoly)
  let dec (x : List Bool) := answer test (out x)
  have hc : ComputableInPolyTime (fun w => w) Computability.encodeBool dec :=
    cpt_comp (f := out) (g := answer test) hout (answer_cpt test hTest)
  refine ⟨dec,?_,hc⟩
  intro x
  let n := x.length+d*depth.eval x.length
  have hlen : len.eval x.length = n := by simp [len,n,Polynomial.eval_add,Polynomial.eval_mul]
  have himage : image.eval x.length = q.eval (3*n+1) := by
    simp [image,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,hlen]
  obtain ⟨S,hS,hSmem⟩ := hSparse (image.eval x.length)
  have hcount : S.card < (unary capPoly x).length := by
    simp only [unary,un_length,capPoly,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_one]
    omega
  have hpad : (unary capPoly x).length * (2*n+1) ≤ (unary padPoly x).length := by
    simp [unary,padPoly,un_length,Polynomial.eval_mul,Polynomial.eval_add,hlen]
  have hlocal (a b : List Bool) (ha : a.length ≤ n) (hb : b.length ≤ n) :
      f (a,b) ∈ S ↔ a ∈ G ∨ b ∈ G := by
    have hl : (f (a,b)).length ≤ image.eval x.length := by
      rw [himage]
      have he : (f (a,b)).length ≤ q.eval (pairB a b).length := by
        simpa only [unpairB_pairB] using hq (pairB a b)
      apply he.trans (eval_mono q ?_)
      rw [pairB_length]
      omega
    simp only [hSmem, hl, and_true, hred]
  obtain ⟨rs,hr,_,hreach,hyes⟩ := run_invariant f B branch henc G S x
    (unary capPoly x) (unary padPoly x) d n hcount hpad hg hB hlocal
    (depth.eval x.length) (by rfl)
  have heval : out x = wire rs := by
    unfold out run
    have hdepth : (unary depth x).length = depth.eval x.length := un_length _
    rw [hdepth,hr]
    simp only [records,pack,unpairB_pairB]
  change x ∈ G ↔ answer test (out x) = true
  rw [heval,answer_enc,← hyes]
  constructor
  · rintro ⟨y,hy,hyG⟩
    exact ⟨y,hy,(hLeaf x y (hreach y hy)).mpr hyG⟩
  · rintro ⟨y,hy,ht⟩
    exact ⟨y,hy,(hLeaf x y (hreach y hy)).mp ht⟩
