import PEqualNP.Outside.WitnessSearchOfCollapse
import PEqualNP.Outside.SparseHardFrontier
import PEqualNP.Outside.SparsePruningMachine
import PEqualNP.Outside.FrontierExpansionMachine
import PEqualNP.Library.L010

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
local notation "Word" => List Bool
local notation "Verifier" => List Bool × List Bool → Bool

namespace SparseFrontierSupport

def children (v : Verifier) (s : Word) : List Word :=
  let (x, w) := unpairB s
  if v (x, w) then [s]
  else [pairB x (w ++ [false]), pairB x (w ++ [true])]

theorem children_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    CPT (fun s => encodeFrontier (children v s)) := by
  have h₀ := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [false]))
  have h₁ := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [true]))
  have hstop := cpt_bitFlag (cpt_comp cpt_unpairB hv)
  refine bf_cptl
    (cpt_sel hstop (cpt_pairB2 h₀ (cpt_pairB2 h₁ (cpt_const [])))
      (cpt_pairB2 cpt_id (cpt_const []))) ?_
  intro s
  cases h : v (unpairB s) <;> simp [children, encodeFrontier, h, bflag]

theorem child_extension (v : Verifier) (x w : Word) :
    (∃ y ∈ children v (pairB x w), y ∈ prefixExtension v) ↔
      pairB x w ∈ prefixExtension v := by
  by_cases ha : v (x, w) = true
  · simp [children, unpairB_pairB, ha]
  · constructor
    · rintro ⟨z, hz, hm⟩
      have he : z = pairB x (w ++ [false]) ∨ z = pairB x (w ++ [true]) := by
        simpa [children, unpairB_pairB, ha] using hz
      rcases he with rfl | rfl
      · obtain ⟨t, ht⟩ := (prefixExtension_pair v x (w ++ [false])).mp hm
        exact (prefixExtension_pair _ _ _).mpr ⟨false :: t, by simpa [List.append_assoc] using ht⟩
      · obtain ⟨t, ht⟩ := (prefixExtension_pair v x (w ++ [true])).mp hm
        exact (prefixExtension_pair _ _ _).mpr ⟨true :: t, by simpa [List.append_assoc] using ht⟩
    · intro h
      obtain ⟨t, ht⟩ := (prefixExtension_pair _ _ _).mp h
      cases t with
      | nil => simp [ha] at ht
      | cons b t =>
        refine ⟨pairB x (w ++ [b]), ?_, (prefixExtension_pair v x _).mpr
          ⟨t, by simpa [List.append_assoc] using ht⟩⟩
        cases b <;> simp [children, unpairB_pairB, ha]

def atDepth (v : Verifier) (x : Word) (k : Nat) (s : Word) : Prop :=
  ∃ w : Word, s = pairB x w ∧ w.length ≤ k ∧ (v (x,w) = true ∨ w.length = k)

theorem children_depth (v : Verifier) (x : Word) (k : Nat)
    {s t : Word} (hs : atDepth v x k s) (ht : t ∈ children v s) :
    atDepth v x (k + 1) t := by
  obtain ⟨w, rfl, hlen, hfin⟩ := hs
  by_cases h : v (x,w) = true
  · have e : t = pairB x w := by simpa [children, unpairB_pairB, h] using ht
    exact ⟨w, e, by omega, Or.inl h⟩
  · have he : w.length = k := hfin.resolve_left h
    have cases : t = pairB x (w ++ [false]) ∨ t = pairB x (w ++ [true]) := by
      simpa [children, unpairB_pairB, h] using ht
    rcases cases with e | e
    · exact ⟨w ++ [false], e, by simp [he], Or.inr (by simp [he])⟩
    · exact ⟨w ++ [true], e, by simp [he], Or.inr (by simp [he])⟩

theorem frontierSize (n : Nat) (xs : List Word) (hl : ∀ x ∈ xs, x.length ≤ n) :
    (encodeFrontier xs).length ≤ (2 * n + 1) * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (pairB x (encodeFrontier xs)).length ≤ (2 * n + 1) * (xs.length + 1)
    rw [pairB_length, Nat.mul_succ]
    have hx := hl x List.mem_cons_self
    have ht := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    omega

def boundedStep (expand prune : Word → Word) (s : Word) : Word :=
  let cap := (unpairB s).1
  let b := (unpairB (unpairB s).2).1
  let front := (unpairB (unpairB s).2).2
  let next := prune (pairB b (expand front))
  sel (bflag (decide (next.length ≤ cap.length))) s (pairB cap (pairB b next))

private def boundedMeasure (s : Word) : Nat := (unpairB s).1.length + 2

private theorem boundedMeasure_step (expand prune : Word → Word) (s : Word) :
    boundedMeasure (boundedStep expand prune s) ≤ boundedMeasure s := by
  unfold boundedStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [boundedMeasure, unpairB_pairB]

private theorem boundedStep_size (expand prune : Word → Word) (s : Word) :
    (boundedStep expand prune s).length ≤ s.length + boundedMeasure s := by
  have hs := unpairB_length s
  have hr := unpairB_length (unpairB s).2
  unfold boundedStep boundedMeasure
  dsimp only
  unfold sel
  split
  · omega
  · rename_i hn
    have hc := (not_congr (bflag_eq_nil _)).mp hn
    simp only [Bool.not_eq_false, decide_eq_true_eq] at hc
    simp only [pairB_length]
    omega

private theorem boundedStep_cpt {expand prune : Word → Word}
    (he : CPT expand) (hp : CPT prune) : CPT (boundedStep expand prune) := by
  have hc := cpt_unpairB1
  have hb := cpt_unpairB1_1 cpt_unpairB2
  have ht := cpt_unpairB2_1 cpt_unpairB2
  have hn := cpt_comp (cpt_pairB2 hb (cpt_comp ht he)) hp
  have hg := cpt_bitFlag (cpt_comp (cpt_pair hc hn) LenCmp.lenLE_polyTime)
  exact bf_cptl (cpt_sel hg cpt_id (cpt_pairB2 hc (cpt_pairB2 hb hn))) (fun _ => rfl)

theorem boundedIter_cpt {expand prune init clock : Word → Word}
    (he : CPT expand) (hp : CPT prune) (hi : CPT init) (hc : CPT clock) :
    CPT (fun x => (boundedStep expand prune)^[(clock x).length] (init x)) := by
  obtain ⟨c⟩ := boundedStep_cpt he hp
  have h := Iter.iter_polyTime_measure (boundedStep expand prune) c boundedMeasure 2
    (boundedMeasure_step expand prune) (boundedStep_size expand prune) (fun s => by
      have h := unpairB_length s
      unfold boundedMeasure
      omega)
  exact bf_cptl (cpt_comp (cpt_pair hi hc) h) (fun _ => rfl)

private def leafImage (v : Verifier) (p : Word × Word) : Word :=
  bflag (v (unpairB p.2))

private theorem leafImage_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair (fun x => x) (leafImage v) :=
  bf_cptl (cpt_bitFlag (cpt_comp (cpt_comp cpt_snd cpt_unpairB) hv)) (fun _ => rfl)

def leafTest (v : Verifier) (s : Word) : Bool :=
  imageLookup (leafImage v) (pairB [] (pairB [true] s))

theorem leafTest_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool (leafTest v) :=
  bf_cptl (cpt_comp (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const [true]) cpt_id))
    (imageLookup_polyTime (leafImage_cpt hv))) (fun _ => rfl)

theorem leafTest_spec (v : Verifier) (xs : List Word) :
    leafTest v (encodeFrontier xs) = true ↔ ∃ y ∈ xs, v (unpairB y) = true := by
  change imageLookup (leafImage v) (pairB [] (pairB [true] (xs.foldr pairB []))) = true ↔ _
  rw [imageLookup_spec]
  simp only [leafImage, bflag]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, by cases hv : v (unpairB y) <;> simp [hv] at h ⊢⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, by simp [h]⟩

end SparseFrontierSupport

open SparseFrontierSupport

private theorem decideSparse {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat)
    (bound : ∀ x w : Word, v (x,w) = true → w.length ≤ p.eval x.length)
    (B : Language Bool) (hB : NPHard B) (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  obtain ⟨f, hf, fSpec⟩ := DisjunctiveHardImage (prefixExtension v) B
    (prefixExtension_np hv p bound) hB
  obtain ⟨r, hr⟩ := disjunctiveImageLength_poly hf
  obtain ⟨prune, hp, hprune⟩ := SparsePruningMachine f hf
  let g : Word → Word := fun s => encodeFrontier (children v s)
  obtain ⟨a, ha⟩ := output_length_poly g (children_cpt hv)
  let expand := expandFrontier g a
  have he : CPT expand := expandFrontier_polyTime (children_cpt hv) a
  have exSpec (xs : List Word) : expand (encodeFrontier xs) =
      encodeFrontier (xs.flatMap (children v)) :=
    expandFrontier_spec (children v) g (fun _ => rfl) a ha xs
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let count : Polynomial Nat := q.comp (r.comp (Polynomial.C 2 * width))
  let cap : Polynomial Nat := (Polynomial.C 2 * width + 1) * (count + 1)
  let state := fun (x : Word) (xs : List Word) => pairB (un (cap.eval (List.length x)))
    (pairB (un (count.eval (List.length x))) (encodeFrontier xs))
  let initial := fun x : Word => state x [pairB x []]
  have hinit : CPT initial :=
    cpt_pairB2 (L055 cap) (cpt_pairB2 (L055 count)
      (cpt_pairB2 (cpt_pairB2 cpt_id (cpt_const [])) (cpt_const [])))
  let run := fun x : Word =>
    (boundedStep expand prune)^[p.eval x.length] (initial x)
  have hruncpt : CPT run :=
    bf_cptl (boundedIter_cpt he hp hinit (L055 p)) (fun x => by simp [run])
  let check := fun x : Word => leafTest v ((unpairB (unpairB (run x)).2).2)
  have hcpt : ComputableInPolyTime (fun x => x) Computability.encodeBool check :=
    cpt_comp (cpt_unpairB2_1 (cpt_unpairB2_1 hruncpt)) (leafTest_cpt hv)
  refine ⟨check, fun x => ?_, hcpt⟩
  have widthSpec : width.eval x.length = 2 * x.length + p.eval x.length + 1 := by
    simp [width]
  have candidateLen (k : Nat) (hk : k ≤ p.eval x.length) (y : Word)
      (hy : atDepth v x k y) : y.length ≤ width.eval x.length := by
    obtain ⟨w, rfl, hlen, _⟩ := hy
    rw [pairB_length, widthSpec]
    omega
  have sparseImages (xs : List Word) (hx : ∀ y ∈ xs, y.length ≤ width.eval x.length) :
      ∀ a ∈ xs, ∀ zs : Finset Word,
        (∀ y ∈ zs, y ∈ B ∧ ∃ w ∈ xs, f (a,w) = y) → zs.card ≤ count.eval x.length := by
    intro a ha zs hzs
    have hc : zs.card ≤ q.eval (r.eval (2 * width.eval x.length)) := by
      apply sparse _ zs
      intro y hy
      obtain ⟨hyB, w, hw, rfl⟩ := hzs y hy
      have ea := hx a ha
      have ew := hx w hw
      exact ⟨hyB, (hr a w).trans (eval_mono r (by omega))⟩
    simpa [count, Polynomial.eval_comp] using hc
  have capSpec : cap.eval x.length =
      (2 * width.eval x.length + 1) * (count.eval x.length + 1) := by simp [cap]
  have invariant (k : Nat) (hk : k ≤ p.eval x.length) :
      ∃ xs : List Word,
        (boundedStep expand prune)^[k] (initial x) = state x xs ∧
        (∀ y ∈ xs, atDepth v x k y) ∧
        ((∃ y ∈ xs, y ∈ prefixExtension v) ↔ ∃ w : Word, v (x,w) = true) := by
    induction k with
    | zero =>
      refine ⟨[pairB x []], rfl, ?_, ?_⟩
      · intro y hy
        have e : y = pairB x [] := by simpa using hy
        exact ⟨[], e, le_rfl, Or.inr rfl⟩
      · simpa using prefixExtension_pair v x []
    | succ k ih =>
      obtain ⟨xs, hstate, hdep, hequiv⟩ := ih (by omega)
      let zs := xs.flatMap (children v)
      have hz (y : Word) (hy : y ∈ zs) : atDepth v x (k + 1) y := by
        obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp hy
        exact children_depth v x k (hdep u hu) ht
      have hlen (y : Word) (hy : y ∈ zs) : y.length ≤ width.eval x.length :=
        candidateLen (k + 1) hk y (hz y hy)
      have hc := hprune (prefixExtension v) B fSpec (count.eval x.length) zs (sparseImages zs hlen)
      change ∃ ys : List Word, ys.Sublist zs ∧ ys.length ≤ count.eval x.length + 1 ∧
        prune (pairB (un (count.eval x.length)) (encodeFrontier zs)) = encodeFrontier ys ∧
        ((∃ y ∈ ys, y ∈ prefixExtension v) ↔ ∃ z ∈ zs, z ∈ prefixExtension v) at hc
      obtain ⟨ys, hsub, hsize, hpr, hpSpec⟩ := hc
      have hcap : (encodeFrontier ys).length ≤ cap.eval x.length := by
        rw [capSpec]
        exact (frontierSize _ ys (fun y hy => hlen y (hsub.subset hy))).trans
          (Nat.mul_le_mul_left _ hsize)
      have hstep : boundedStep expand prune (state x xs) = state x ys := by
        have ex : expand (encodeFrontier xs) = encodeFrontier zs := exSpec xs
        simp [boundedStep, state, unpairB_pairB, ex, hpr, bflag, hcap, un_length]
      have hchildren : (∃ z ∈ zs, z ∈ prefixExtension v) ↔ ∃ u ∈ xs, u ∈ prefixExtension v := by
        constructor
        · rintro ⟨z, hzmem, hza⟩
          obtain ⟨u, hu, hchild⟩ := List.mem_flatMap.mp hzmem
          obtain ⟨w, rfl, _, _⟩ := hdep u hu
          exact ⟨pairB x w, hu, (child_extension v x w).mp ⟨z, hchild, hza⟩⟩
        · rintro ⟨u, hu, hua⟩
          obtain ⟨w, rfl, _, _⟩ := hdep u hu
          obtain ⟨z, hzchild, hza⟩ := (child_extension v x w).mpr hua
          exact ⟨z, List.mem_flatMap.mpr ⟨pairB x w, hu, hzchild⟩, hza⟩
      refine ⟨ys, ?_, fun y hy => hz y (hsub.subset hy),
        hpSpec.trans (hchildren.trans hequiv)⟩
      rw [Function.iterate_succ_apply', hstate, hstep]
  obtain ⟨xs, hx, hdep, hequiv⟩ := invariant (p.eval x.length) le_rfl
  change (∃ w : Word, v (x,w) = true) ↔ check x = true
  have hout : check x = leafTest v (encodeFrontier xs) := by
    simp only [check, run, hx, state, unpairB_pairB]
  rw [hout, leafTest_spec]
  refine hequiv.symm.trans ?_
  constructor
  · rintro ⟨y, hy, hmem⟩
    obtain ⟨w, rfl, _, hs⟩ := hdep y hy
    refine ⟨pairB x w, hy, ?_⟩
    rw [unpairB_pairB]
    rcases hs with ha | hl
    · exact ha
    · obtain ⟨t, ht⟩ := (prefixExtension_pair v x w).mp hmem
      have hn := bound x (w ++ t) ht
      have hnil : t = [] := List.length_eq_zero_iff.mp (by rw [List.length_append] at hn; omega)
      simpa [hnil] using ht
  · rintro ⟨y, hy, h⟩
    obtain ⟨w, rfl, _, _⟩ := hdep y hy
    rw [unpairB_pairB] at h
    exact ⟨pairB x w, hy, (prefixExtension_pair v x w).mpr ⟨[], by simpa using h⟩⟩

/-- Mahaney's implication for cumulative sparsity under the exact reference machine model. -/
theorem SparseHardImpliesCollapse (B : Language Bool) (hB : NPHard B) (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro A hA
  obtain ⟨R, p, ⟨v, spec, hv⟩, bound, hc⟩ := L045 A hA
  have hnorm (x w : Word) (h : v (x,w) = true) : w.length ≤ p.eval x.length :=
    bound x w ((spec (x,w)).mpr h)
  have he : A = ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) :=
    Set.ext (fun x => (hc x).trans (exists_congr (fun w => spec (x,w))))
  rw [he]
  exact decideSparse hv p hnorm B hB q sparse

end PEqualNP.Outside
