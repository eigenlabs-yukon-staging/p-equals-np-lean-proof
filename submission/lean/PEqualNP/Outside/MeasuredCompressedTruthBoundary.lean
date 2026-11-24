import PEqualNP.Outside.CompressedVariableTruthBoundary

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)
local notation "PairCPT" => ComputableInPolyTime encodePair (fun x : Word => x)
local notation "BoolCPT" => ComputableInPolyTime (fun x : Word => x) Computability.encodeBool

private theorem mergeMachines {source left right : Word × Word → Word}
    (hs : PairCPT source) (hl : PairCPT left) (hr : PairCPT right) :
    ∃ merge : Word × Word → Word, PairCPT merge ∧
      ∀ (p : Word × Word) (xs ls rs : List Word),
        source p = encodeFrontier xs → left p = encodeFrontier ls → right p = encodeFrontier rs →
        merge p = encodeFrontier (mergeSelections xs ls rs) := by
  let pred := fun p : Word × Word => encodedMember p.1 p.2
  have hp : ComputableInPolyTime encodePair Computability.encodeBool pred :=
    cpt_fromRawBool (encodedMember_cpt cpt_unpairB1 cpt_unpairB2)
  obtain ⟨out, ho, hout⟩ := FrontierFilterByParameter pred hp
  let merge := fun p : Word × Word => out (left p ++ right p, source p)
  have hmerge : PairCPT merge := by
    have h := cpt_comp (cpt_pair
      (cpt_app2 (cpt_comp cpt_unpairB hl) (cpt_comp cpt_unpairB hr))
      (cpt_comp cpt_unpairB hs)) ho
    exact cpt_fromRaw (f := merge) h
  refine ⟨merge,hmerge,fun p xs ls rs hs' hl' hr' => ?_⟩
  unfold merge
  rw [hs', hl', hr', ← encodeFrontier_append_words]
  have hn : out (encodeFrontier (ls ++ rs), encodeFrontier xs) = encodeFrontier
      (xs.filter (fun x => encodedMember (encodeFrontier (ls ++ rs)) x)) := hout _ _
  rw [hn]
  change encodeFrontier (xs.filter (fun x => encodedMember (encodeFrontier (ls ++ rs)) x)) = _
  congr 1
  apply congrArg (fun pred => xs.filter pred)
  funext x
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using encodedMember_spec (ls ++ rs) x

private theorem compileDefaultTrim {k : Nat} (t : CandidateTable k)
    (h : BoolCPT (fun x => t x (fun _ => false))) :
    ∃ run : Word × Word → Word, PairCPT run ∧
      ∀ (n : Word) (xs : List Word),
        run (n,encodeFrontier xs) = encodeFrontier (trimByDefault t n.length xs) := by
  have neg : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime _ _ _ (fun b => some (!b)) (fun b => by cases b <;> rfl)
  have group (d : Bool) : ∃ run : Word × Word → Word, PairCPT run ∧
      ∀ (n : Word) (xs : List Word),
        run (n,encodeFrontier xs) = encodeFrontier (defaultBucket t d xs) := by
    have hgroup : BoolCPT (fun x => t x (fun _ => false) == d) := by
      cases d
      · exact bf_cptl (cpt_comp h neg) (fun x => by cases t x (fun _ => false) <;> rfl)
      · exact bf_cptl h (fun x => by cases t x (fun _ => false) <;> rfl)
    exact FrontierFilterByParameter _ (cpt_comp (g := fun x => t x (fun _ => false) == d) cpt_snd hgroup)
  obtain ⟨f0,h0,hs0⟩ := group false
  obtain ⟨f1,h1,hs1⟩ := group true
  obtain ⟨trim, ht, hts⟩ := TrimEncodedFrontier
  let l := fun p : Word × Word => trim (p.1, f0 p)
  let r := fun p : Word × Word => trim (p.1, f1 p)
  have hl : PairCPT l := by
    have hc := cpt_comp (cpt_pair cpt_unpairB1 (cpt_comp cpt_unpairB h0)) ht
    exact cpt_fromRaw (f := l) hc
  have hr : PairCPT r := by
    have hc := cpt_comp (cpt_pair cpt_unpairB1 (cpt_comp cpt_unpairB h1)) ht
    exact cpt_fromRaw (f := r) hc
  have hts' (n : Word) (xs : List Word) :
      trim (n, encodeFrontier xs) = encodeFrontier (trimBoundary n.length xs) := hts n xs
  obtain ⟨run,hc,spec⟩ := mergeMachines cpt_snd hl hr
  refine ⟨run,hc,fun n xs => ?_⟩
  exact spec _ xs _ _ rfl
    (by simp [l,hs0,hts']) (by simp [r,hs1,hts'])

private theorem foldCpt {α : Type} (xs : List α) (step : α → Word → Word)
    (hc : ∀ a, CPT (step a)) :
    CPT (fun s => xs.foldl (fun w x => step x w) s) := by
  induction xs with
  | nil => exact cpt_id
  | cons a as ih => exact cpt_comp (hc a) ih

private def workingState (b : Word) (original current : List Word) : Word :=
  pairB b (pairB (encodeFrontier original) (encodeFrontier current))

private def coordinateStep {k : Nat} (implement : Fin k → Word → Word)
    (i : Fin k) (s : Word) : Word :=
  pairB (unpairB s).1 (pairB (unpairB (unpairB s).2).1 (implement i s))

private theorem coordinateStep_cpt {k : Nat} (implement : Fin k → Word → Word)
    (hc : ∀ i, CPT (implement i)) (i : Fin k) :
    CPT (coordinateStep implement i) :=
  cpt_pairB2 cpt_unpairB1 (cpt_pairB2 (cpt_unpairB1_1 cpt_unpairB2) (hc i))

private theorem coordinateRun {k : Nat} (q : Word → Fin k → Word)
    (thin : Fin k → Nat → List Word → List Word) (implement : Fin k → Word → Word)
    (hs : ∀ (i : Fin k) (b : Word) (todo xs : List Word),
      implement i (workingState b todo xs) = encodeFrontier
        (todo.foldl (fun ys p => compressOneFiber (fun y => q y i) (thin i) b.length p ys) xs))
    (coords : List (Fin k)) (b : Word) (orig curr : List Word) :
    coords.foldl (fun z i => coordinateStep implement i z) (workingState b orig curr) =
      workingState b orig (foldSelectedFibers q (fun i => thin i b.length)
        (coords.flatMap (fun i => orig.map (fun x => (i, q x i)))) curr) := by
  induction coords generalizing curr with
  | nil => rfl
  | cons i rest ih =>
    let next := orig.foldl (fun ys p => compressOneFiber (fun y => q y i) (thin i) b.length p ys) curr
    have hnext : coordinateStep implement i (workingState b orig curr) = workingState b orig next := by
      unfold coordinateStep
      rw [hs i b orig curr]
      simp [workingState, unpairB_pairB, next]
    simp only [List.foldl_cons, hnext, ih, List.flatMap_cons]
    congr 1
    simp [foldSelectedFibers, List.foldl_append, List.foldl_map, selectedFiberStep,
      compressOneFiber, fiberList, next] <;> rfl

private theorem compressedBoundPolynomial (k : Nat) :
    ∃ p : Polynomial Nat, ∀ b, p.eval b = compressedTTBound b k := by
  induction k with
  | zero => exact ⟨Polynomial.C 2, fun b => by simp [compressedTTBound]⟩
  | succ k ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨Polynomial.C 2 * (Polynomial.C 2 *
      (Polynomial.C (k+1) * Polynomial.X * (Polynomial.C 2 * p)) + 1), fun b => ?_⟩
    simp [compressedTTBound,hp]

private theorem compileCompressed (k : Nat) (q : Word → Fin k → Word)
    (t : CandidateTable k) (hq : ∀ i, CPT (fun x => q x i))
    (ht : ∀ a, BoolCPT (fun x => t x a)) :
    ∃ run : Word × Word → Word, PairCPT run ∧
      ∀ (b : Word) (xs : List Word),
        run (b, encodeFrontier xs) = encodeFrontier (keepCompressedBoundary k b.length q t xs) := by
  induction k with
  | zero =>
    obtain ⟨trim, hc, hs⟩ := compileDefaultTrim t (ht (fun _ => false))
    let run := fun p : Word × Word => trim ([],p.2)
    have hrun : PairCPT run := by
      have h := cpt_comp (cpt_pair (cpt_const []) cpt_unpairB2) hc
      exact cpt_fromRaw (f := run) h
    exact ⟨run, hrun, fun b xs => hs [] xs⟩
  | succ k ih =>
    classical
    let thin := fun i n => fiberSelect q t (keepCompressedBoundary k n) i
    have impl (i : Fin (k+1)) :
        ∃ run : Word → Word, CPT run ∧
          ∀ (b : Word) (todo xs : List Word),
            run (workingState b todo xs) =
              encodeFrontier (todo.foldl (fun ys p =>
                compressOneFiber (fun y => q y i) (thin i) b.length p ys) xs) := by
      let q' := fun x j => q x (i.succAbove j)
      have h' (v : Bool) (a : Fin k → Bool) :
          BoolCPT (fun x => restrictTable t i v x a) :=
        ht (Fin.insertNth i v a)
      obtain ⟨l,hl,ls⟩ := ih q' (restrictTable t i false) (fun j => hq (i.succAbove j)) (h' false)
      obtain ⟨r,hr,rs⟩ := ih q' (restrictTable t i true) (fun j => hq (i.succAbove j)) (h' true)
      obtain ⟨run,hc,hs⟩ := mergeMachines cpt_snd hl hr
      exact FiberCompressionPass (fun y => q y i) (hq i) (thin i) run hc
        (fun b xs => hs _ xs _ _ rfl (ls b xs) (rs b xs))
    choose implement hc hs using impl
    obtain ⟨trim,htrim,trimSpec⟩ := compileDefaultTrim t (ht (fun _ => false))
    obtain ⟨bound,hbound⟩ := compressedBoundPolynomial k
    let radius : Polynomial Nat := Polynomial.C (k+1) * Polynomial.X * (Polynomial.C 2 * bound)
    let initial := fun s : Word => pairB (unpairB s).1 (pairB (unpairB s).2 (unpairB s).2)
    let mapped := fun s : Word => (List.finRange (k+1)).foldl
      (fun z i => coordinateStep implement i z) (initial s)
    have hi : CPT initial := cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 cpt_unpairB2)
    have hm : CPT mapped :=
      cpt_comp (g := fun s => (List.finRange (k+1)).foldl
        (fun z i => coordinateStep implement i z) s) hi
        (foldCpt _ _ (coordinateStep_cpt implement hc))
    let run := fun p : Word × Word =>
      trim (un (radius.eval p.1.length), (unpairB (unpairB (mapped (pairB p.1 p.2))).2).2)
    have hrun : PairCPT run := by
      have h := cpt_comp (cpt_pair (cpt_comp cpt_unpairB1 (L055 radius))
        (cpt_unpairB2_1 (cpt_unpairB2_1 hm))) htrim
      refine bf_cptl (cpt_comp cpt_pairB h) ?_
      rintro ⟨b,xs⟩
      simp [run,unpairB_pairB,un]
    refine ⟨run,hrun,fun b xs => ?_⟩
    let ys := foldSelectedFibers q (fun i => thin i b.length) (fiberKeys q xs) xs
    have he : mapped (pairB b (encodeFrontier xs)) = workingState b xs ys := by
      have hinit : initial (pairB b (encodeFrontier xs)) = workingState b xs xs := by
        simp [initial,workingState,unpairB_pairB]
      unfold mapped
      rw [hinit]
      exact coordinateRun q thin implement hs (List.finRange _) b xs xs
    have hy : radius.eval b.length = (k+1) * b.length * (2 * compressedTTBound b.length k) := by
      simp [radius,hbound]
    simp only [run,he,workingState,unpairB_pairB,trimSpec,un_length,hy]
    rfl

/-- The compiler handles an input-dependent table by branching on one bit per
fiber and splitting only on the value at the all-false vector for the trim. -/
theorem MeasuredCompressedTruthBoundary (k : Nat) (q : Word → Fin k → Word)
    (t : CandidateTable k) (hq : ∀ i, CPT (fun x => q x i))
    (ht : ∀ a, BoolCPT (fun x => t x a)) :
    ∃ (run : Word × Word → Word) (prune : Nat → List Word → List Word),
      PairCPT run ∧
      (∀ (b : Word) (xs : List Word),
        let enc := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (b, xs.foldr enc []) = (prune b.length xs).foldr enc []) ∧
      ∀ (b : Nat) (xs : List Word), xs.Nodup →
        (prune b xs).Sublist xs ∧
        (prune b xs).length ≤ Nat.rec 2 (fun i m => 2 * (2 * ((i+1) * b * (2*m)) + 1)) k ∧
        ∀ (S : Finset Word) (l r : List Word) (x : Word), S.card ≤ b → xs = l ++ x :: r →
          (∀ y ∈ l ++ [x], t y (fun i => decide (q y i ∈ S)) = true) →
          (∀ y ∈ r, t y (fun i => decide (q y i ∈ S)) = false) → x ∈ prune b xs := by
  obtain ⟨run,hr,hs⟩ := compileCompressed k q t hq ht
  refine ⟨run,fun b => keepCompressedBoundary k b q t,hr,hs,fun b xs hn => ?_⟩
  obtain ⟨hsub,hlen,hkeep⟩ := compressedBoundarySpec k b q t xs hn
  have eq (i : Nat) : compressedTTBound b i =
      Nat.rec 2 (fun j m => 2 * (2 * ((j+1) * b * (2*m)) + 1)) i := by
    induction i with
    | zero => rfl
    | succ i ih => simp [compressedTTBound, ih]
  refine ⟨hsub, hlen.trans_eq (eq k), fun S l r x hb hh hl hr => ?_⟩
  exact hkeep S x hb ⟨l,r,hh,hl,hr⟩

end PEqualNP.Outside
