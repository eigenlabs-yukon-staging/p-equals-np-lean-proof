import PEqualNP.Outside.BoundedTruthTableBoundary
import PEqualNP.Outside.FiberCompressionPass
import PEqualNP.Outside.TrimEncodedFrontier

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

theorem truthBoundaryBoundPolynomial (k : Nat) :
    ∃ p : Polynomial Nat, ∀ b, p.eval b = ttBound b k := by
  induction k with
  | zero => exact ⟨1, fun b => by simp [ttBound]⟩
  | succ k ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨Polynomial.C (2 * (k+1)) * Polynomial.X * p + 1, fun b => ?_⟩
    simp [ttBound, hp, Nat.mul_assoc]

private theorem foldCpt {α : Type} (xs : List α) (step : α → Word → Word)
    (hc : ∀ a, CPT (step a)) :
    CPT (fun s => xs.foldl (fun w x => step x w) s) := by
  induction xs with
  | nil => exact cpt_id
  | cons a as ih => exact cpt_comp (hc a) ih

private def coordinateStep {k : Nat} (implement : Fin (k+1) → Word → Word)
    (i : Fin (k+1)) (s : Word) : Word :=
  pairB (unpairB s).1 (pairB (unpairB (unpairB s).2).1 (implement i s))

private theorem coordinateStep_cpt {k : Nat} (implement : Fin (k+1) → Word → Word)
    (hc : ∀ i, CPT (implement i)) (i : Fin (k+1)) :
    CPT (coordinateStep implement i) :=
  cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB2) (hc i))

private def workingState (b : Word) (orig curr : List Word) : Word :=
  pairB b (pairB (encodeFrontier orig) (encodeFrontier curr))

private theorem coordinateRun {k : Nat} (q : Word → Fin (k+1) → Word)
    (implement : Fin (k+1) → Word → Word)
    (hspec : ∀ (i : Fin (k+1)) (b : Word) (todo xs : List Word),
      implement i (workingState b todo xs) =
        encodeFrontier (todo.foldl (fun ys pivot =>
          compressOneFiber (fun y => q y i)
            (fun b => keepTruthBoundary k b (fun y j => q y (i.succAbove j))) b.length pivot ys) xs))
    (coords : List (Fin (k+1))) (b : Word) (orig curr : List Word) :
    coords.foldl (fun z i => coordinateStep implement i z) (workingState b orig curr) =
      workingState b orig (takeFibers q (keepTruthBoundary k b.length)
        (coords.flatMap (fun i => orig.map (fun x => (i, q x i)))) curr) := by
  induction coords generalizing curr with
  | nil => rfl
  | cons i is ih =>
    let yz := orig.foldl (fun ys pivot =>
      compressOneFiber (fun y => q y i)
        (fun b => keepTruthBoundary k b (fun y j => q y (i.succAbove j))) b.length pivot ys) curr
    have hh : coordinateStep implement i (workingState b orig curr) = workingState b orig yz := by
      unfold coordinateStep
      rw [hspec i b orig curr]
      simp [workingState, unpairB_pairB, yz]
    simp only [List.foldl_cons, hh, ih, List.flatMap_cons]
    congr 1
    simp [takeFibers, List.foldl_append, List.foldl_map, fiberStep, compressOneFiber, fiberList, yz] <;> rfl

/-- Compile every fixed arity instance of the deterministic fiber algorithm to a
pinned polynomial-time machine on a tagged pair of the budget word and the frontier. -/
theorem compileTruthBoundary (k : Nat) (q : Word → Fin k → Word)
    (hq : ∀ i, CPT (fun x => q x i)) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (b : Word) (xs : List Word),
        run (b, encodeFrontier xs) = encodeFrontier (keepTruthBoundary k b.length q xs) := by
  induction k with
  | zero =>
    obtain ⟨trim, htrim, spec⟩ := TrimEncodedFrontier
    let run := fun p : Word × Word => trim ([],p.2)
    have hc : ComputableInPolyTime encodePair (fun x => x) run := by
      have h : CPT (fun s => trim ([],(unpairB s).2)) :=
        cpt_comp (f := fun s => ([],(unpairB s).2)) (g := trim)
          (cpt_pair (cpt_const []) cpt_unpairB2) htrim
      exact cpt_fromRaw (f := run) h
    refine ⟨run,hc,fun b xs => ?_⟩
    exact spec [] xs
  | succ k ih =>
    classical
    have machine (i : Fin (k+1)) :
        ∃ run : Word → Word, CPT run ∧
          ∀ (b : Word) (todo xs : List Word),
            run (workingState b todo xs) =
              encodeFrontier (todo.foldl (fun ys pivot =>
                compressOneFiber (fun y => q y i)
                  (fun b => keepTruthBoundary k b (fun y j => q y (i.succAbove j))) b.length pivot ys) xs) := by
      let sub := fun (x : Word) (j : Fin k) => q x (i.succAbove j)
      obtain ⟨prune, hp, hspec⟩ := ih sub (fun j => hq (i.succAbove j))
      exact FiberCompressionPass (fun y => q y i) (hq i)
        (fun b => keepTruthBoundary k b sub) prune hp hspec
    choose implement hc hspec using machine
    obtain ⟨trim,htrim,trimSpec⟩ := TrimEncodedFrontier
    obtain ⟨pol,hpol⟩ := truthBoundaryBoundPolynomial k
    let radius : Polynomial Nat := Polynomial.C (k+1) * Polynomial.X * pol
    let inputs := fun s : Word => pairB (unpairB s).1 (pairB (unpairB s).2 (unpairB s).2)
    let mapped := fun s : Word => (List.finRange (k+1)).foldl
      (fun z i => coordinateStep implement i z) (inputs s)
    have hin : CPT inputs :=
      cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 cpt_unpairB2)
    have hm : CPT mapped :=
      cpt_comp (g := fun s => (List.finRange (k+1)).foldl
        (fun z i => coordinateStep implement i z) s) hin
        (foldCpt _ _ (coordinateStep_cpt implement hc))
    let run := fun p : Word × Word =>
      trim (un (radius.eval p.1.length), (unpairB (unpairB (mapped (pairB p.1 p.2))).2).2)
    have hr : ComputableInPolyTime encodePair (fun x => x) run := by
      have h := cpt_comp (cpt_pair (cpt_comp cpt_unpairB1 (L055 radius))
        (cpt_unpairB2_1 (cpt_unpairB2_1 hm))) htrim
      refine bf_cptl (cpt_comp cpt_pairB h) ?_
      rintro ⟨b,xs⟩
      simp [run, unpairB_pairB, un]
    refine ⟨run,hr,fun b xs => ?_⟩
    let ys := takeFibers q (keepTruthBoundary k b.length) (fiberKeys q xs) xs
    have hm' : mapped (pairB b (encodeFrontier xs)) = workingState b xs ys := by
      simpa only [mapped, inputs, unpairB_pairB, workingState, ys, fiberKeys] using
        coordinateRun q implement hspec (List.finRange (k+1)) b xs xs
    have hv : radius.eval b.length = (k+1)*b.length*ttBound b.length k := by simp [radius,hpol]
    change trim (un (radius.eval b.length), (unpairB (unpairB
      (mapped (pairB b (encodeFrontier xs)))).2).2) = _
    rw [hm']
    simp only [workingState, unpairB_pairB]
    have h : trim (un (radius.eval b.length), encodeFrontier ys) =
        encodeFrontier (trimBoundary ((un (radius.eval b.length)).length) ys) :=
      trimSpec (un (radius.eval b.length)) ys
    simpa only [hv, un_length, keepTruthBoundary, ys] using h


/-- The width and boundary guarantees of the fixed-arity list algorithm hold for
the output of a pinned polynomial-time machine on the encoded frontier. -/
theorem MeasuredBoundedTruthTableBoundary (k : Nat) (q : Word → Fin k → Word)
    (hq : ∀ i, CPT (fun x => q x i)) :
    ∃ (run : Word × Word → Word) (prune : Nat → List Word → List Word) (bound : Polynomial Nat),
      ComputableInPolyTime encodePair (fun x => x) run ∧
      (∀ (b : Word) (xs : List Word),
        let enc := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (b, xs.foldr enc []) = (prune b.length xs).foldr enc []) ∧
      ∀ (b : Nat) (xs : List Word), xs.Nodup →
        (prune b xs).Sublist xs ∧ (prune b xs).length ≤ bound.eval b ∧
        ∀ (S : Finset Word) (T : (Fin k → Bool) → Bool)
          (left right : List Word) (x : Word), S.card ≤ b →
          xs = left ++ x::right →
          (∀ y ∈ left ++ [x], T (fun i => decide (q y i ∈ S)) = true) →
          (∀ y ∈ right, T (fun i => decide (q y i ∈ S)) = false) →
          x ∈ prune b xs := by
  obtain ⟨run, hr, hs⟩ := compileTruthBoundary k q hq
  obtain ⟨bound, hbound⟩ := truthBoundaryBoundPolynomial k
  refine ⟨run,fun b => keepTruthBoundary k b q,bound,hr,hs,fun b xs hn => ?_⟩
  obtain ⟨hsub,hlen,hbranch⟩ := truthBoundarySpec k b q xs hn
  refine ⟨hsub, (hbound b).symm ▸ hlen, fun S T ls rs x hb he hy hn' => ?_⟩
  exact hbranch S T x hb ⟨ls,rs,he,hy,hn'⟩

end PEqualNP.Outside
