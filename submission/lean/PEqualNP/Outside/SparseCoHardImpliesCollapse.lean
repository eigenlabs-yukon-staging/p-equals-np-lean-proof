import PEqualNP.Outside.SparseHardImpliesCollapse
import PEqualNP.Outside.ConjunctiveCoHardImage
import PEqualNP.Outside.CoSparsePruningMachine

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open SparseFrontierSupport

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Word" => List Bool
local notation "Verifier" => List Bool × List Bool → Bool

private def terminal : Word := pairB [true] []

private def expandFlagged (expand : Word → Word) (s : Word) : Word :=
  sel (unpairB s).1 (pairB [] (expand (unpairB s).2)) s

private theorem expandFlagged_cpt {expand : Word → Word} (he : CPT expand) :
    CPT (expandFlagged expand) :=
  bf_cptl (cpt_sel cpt_unpairB1 (cpt_pairB2 (cpt_const []) (cpt_comp cpt_unpairB2 he))
    cpt_id) (fun _ => rfl)

private def pruneFlagged (prune : Word → Word) (s : Word) : Word :=
  let b := (unpairB s).1
  let inner := (unpairB s).2
  sel (unpairB inner).1 (prune (pairB b (unpairB inner).2)) inner

private theorem pruneFlagged_cpt {prune : Word → Word} (hp : CPT prune) :
    CPT (pruneFlagged prune) :=
  bf_cptl (cpt_sel (cpt_unpairB1_1 cpt_unpairB2)
    (cpt_comp (cpt_pairB2 cpt_unpairB1 (cpt_unpairB2_1 cpt_unpairB2)) hp) cpt_unpairB2)
    (fun _ => rfl)

private theorem terminal_fixed (expand prune : Word → Word) (cap b : Word) :
    boundedStep (expandFlagged expand) (pruneFlagged prune) (pairB cap (pairB b terminal)) =
      pairB cap (pairB b terminal) := by
  by_cases h : terminal.length ≤ cap.length <;>
    simp [boundedStep, expandFlagged, pruneFlagged, terminal, unpairB_pairB, sel, bflag, h]

private def checkFlagged (v : Verifier) (s : Word) : Bool :=
  !((unpairB s).1 ++ bflag (leafTest v (unpairB s).2)).isEmpty

private theorem checkFlagged_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool (checkFlagged v) :=
  bf_cptl (cpt_comp (cpt_app2 cpt_unpairB1
      (cpt_bitFlag (cpt_comp cpt_unpairB2 (leafTest_cpt hv)))) bf_cpt_neL) (fun _ => rfl)

private theorem checkFlagged_live (v : Verifier) (xs : List Word) :
    checkFlagged v (pairB [] (encodeFrontier xs)) = true ↔ ∃ y ∈ xs, v (unpairB y) = true := by
  simp only [checkFlagged, unpairB_pairB, List.nil_append]
  have h (b : Bool) : (!(bflag b).isEmpty) = b := by cases b <;> rfl
  rw [h, leafTest_spec]

private theorem checkFlagged_terminal (v : Verifier) : checkFlagged v terminal = true := by
  simp [checkFlagged, terminal, unpairB_pairB]

/-- A polynomial-time frontier operation that either certifies a yes input or preserves
existence while shrinking the frontier suffices for deterministic verifier search. -/
theorem decideFlaggedSparse {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat)
    (bound : ∀ x w : Word, v (x,w) = true → w.length ≤ p.eval x.length)
    (count : Polynomial Nat) (prune : Word → Word) (hp : CPT prune)
    (hprune : ∀ (n : Nat) (xs : List Word), (∀ y ∈ xs, y.length ≤ 2*n + p.eval n + 1) →
      let out := prune (pairB (un (count.eval n)) (encodeFrontier xs))
      (out = pairB [true] [] ∧ ∃ z ∈ xs, z ∈ prefixExtension v) ∨
        (∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ count.eval n + 1 ∧
          out = pairB [] (encodeFrontier ys) ∧
            ((∃ y ∈ ys, y ∈ prefixExtension v) ↔ ∃ z ∈ xs, z ∈ prefixExtension v))) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  let g : Word → Word := fun s => encodeFrontier (children v s)
  obtain ⟨a, ha⟩ := output_length_poly g (children_cpt hv)
  let expand := expandFrontier g a
  have he : CPT expand := expandFrontier_polyTime (children_cpt hv) a
  have exSpec (xs : List Word) : expand (encodeFrontier xs) =
      encodeFrontier (xs.flatMap (children v)) :=
    expandFrontier_spec (children v) g (fun _ => rfl) a ha xs
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let cap : Polynomial Nat := (Polynomial.C 2 * width + 1) * (count + 1) + Polynomial.C 3
  let state := fun (x : Word) (f : Word) =>
    pairB (un (cap.eval x.length)) (pairB (un (count.eval x.length)) f)
  let live := fun (xs : List Word) => pairB [] (encodeFrontier xs)
  let initial := fun x : Word => state x (live [pairB x []])
  have hinit : CPT initial :=
    cpt_pairB2 (L055 cap) (cpt_pairB2 (L055 count)
      (cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_pairB2 cpt_id (cpt_const [])) (cpt_const []))))
  let step := boundedStep (expandFlagged expand) (pruneFlagged prune)
  let run := fun x : Word => step^[p.eval x.length] (initial x)
  have hruncpt : CPT run :=
    bf_cptl (boundedIter_cpt (expandFlagged_cpt he) (pruneFlagged_cpt hp) hinit (L055 p))
      (fun x => by simp [run, step])
  let check := fun x : Word => checkFlagged v ((unpairB (unpairB (run x)).2).2)
  have hcpt : ComputableInPolyTime (fun x => x) Computability.encodeBool check :=
    cpt_comp (cpt_unpairB2_1 (cpt_unpairB2_1 hruncpt)) (checkFlagged_cpt hv)
  refine ⟨check, fun x => ?_, hcpt⟩
  have widthSpec : width.eval x.length = 2 * x.length + p.eval x.length + 1 := by
    simp [width]
  have candidateLen (k : Nat) (hk : k ≤ p.eval x.length) (y : Word)
      (hy : atDepth v x k y) : y.length ≤ width.eval x.length := by
    obtain ⟨w, rfl, hlen, _⟩ := hy
    rw [pairB_length, widthSpec]
    omega
  have capSpec : cap.eval x.length =
      (2 * width.eval x.length + 1) * (count.eval x.length + 1) + 3 := by simp [cap]
  have invariant (k : Nat) (hk : k ≤ p.eval x.length) :
      (step^[k] (initial x) = state x terminal ∧ ∃ w : Word, v (x,w) = true) ∨
      ∃ xs : List Word, step^[k] (initial x) = state x (live xs) ∧
        (∀ y ∈ xs, atDepth v x k y) ∧
        ((∃ y ∈ xs, y ∈ prefixExtension v) ↔ ∃ w : Word, v (x,w) = true) := by
    induction k with
    | zero =>
      right
      refine ⟨[pairB x []], rfl, ?_, ?_⟩
      · intro y hy
        have e : y = pairB x [] := by simpa using hy
        exact ⟨[], e, le_rfl, Or.inr rfl⟩
      · simpa using prefixExtension_pair v x []
    | succ k ih =>
      rcases ih (by omega) with ⟨hterm, hyes⟩ | ⟨xs, hstate, hdep, hequiv⟩
      · left
        refine ⟨?_, hyes⟩
        rw [Function.iterate_succ_apply', hterm]
        exact terminal_fixed expand prune _ _
      · let zs := xs.flatMap (children v)
        have hz (y : Word) (hy : y ∈ zs) : atDepth v x (k + 1) y := by
          obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp hy
          exact children_depth v x k (hdep u hu) ht
        have hlen (y : Word) (hy : y ∈ zs) : y.length ≤ width.eval x.length :=
          candidateLen (k + 1) hk y (hz y hy)
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
        have hc := hprune x.length zs (fun y hy => (hlen y hy).trans_eq widthSpec)
        change
          (prune (pairB (un (count.eval x.length)) (encodeFrontier zs)) = terminal ∧
            ∃ z ∈ zs, z ∈ prefixExtension v) ∨
          (∃ ys : List Word, ys.Sublist zs ∧ ys.length ≤ count.eval x.length + 1 ∧
            prune (pairB (un (count.eval x.length)) (encodeFrontier zs)) = live ys ∧
              ((∃ y ∈ ys, y ∈ prefixExtension v) ↔ ∃ z ∈ zs, z ∈ prefixExtension v)) at hc
        have nextStep (o : Word)
            (hpr : prune (pairB (un (count.eval x.length)) (encodeFrontier zs)) = o)
            (hcap : o.length ≤ cap.eval x.length) : step (state x (live xs)) = state x o := by
          have ex : expand (encodeFrontier xs) = encodeFrontier zs := exSpec xs
          simp [step, boundedStep, expandFlagged, pruneFlagged, state, live, unpairB_pairB,
            ex, hpr, bflag, hcap, un_length]
        rcases hc with ⟨hout, hyes⟩ | ⟨ys, hsub, hsize, hpr, hpSpec⟩
        · left
          refine ⟨?_, (hchildren.trans hequiv).mp hyes⟩
          have ht : terminal.length ≤ cap.eval x.length := by
            rw [capSpec]
            simp only [terminal, pairB_length, List.length_cons, List.length_nil]
            omega
          rw [Function.iterate_succ_apply', hstate, nextStep terminal hout ht]
        · right
          refine ⟨ys, ?_, fun y hy => hz y (hsub.subset hy),
            hpSpec.trans (hchildren.trans hequiv)⟩
          have hcap : (live ys).length ≤ cap.eval x.length := by
            have h := (frontierSize _ ys (fun y hy => hlen y (hsub.subset hy))).trans
              (Nat.mul_le_mul_left _ hsize)
            simp only [live, pairB_length, capSpec, List.length_nil, Nat.mul_zero, Nat.zero_add]
            omega
          rw [Function.iterate_succ_apply', hstate, nextStep (live ys) hpr hcap]
  change (∃ w : Word, v (x,w) = true) ↔ check x = true
  rcases invariant (p.eval x.length) le_rfl with ⟨hs, hyes⟩ | ⟨xs, hx, hdep, hequiv⟩
  · have hout : check x = checkFlagged v terminal := by
      simp only [check, run, hs, state, unpairB_pairB]
    rw [hout, checkFlagged_terminal]
    simp [hyes]
  · have hout : check x = checkFlagged v (live xs) := by
      simp only [check, run, hx, state, unpairB_pairB]
    rw [hout, checkFlagged_live]
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

private theorem decideCoSparse {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) (p : Polynomial Nat)
    (bound : ∀ x w : Word, v (x,w) = true → w.length ≤ p.eval x.length)
    (B : Language Bool) (hB : ∀ L ∈ coNP, PolyTimeReducible L B) (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  obtain ⟨f, hf, fSpec⟩ := ConjunctiveCoHardImage (prefixExtension v) B
    (prefixExtension_np hv p bound) hB
  obtain ⟨r, hr⟩ := disjunctiveImageLength_poly hf
  obtain ⟨prune, hp, hprune⟩ := CoSparsePruningMachine f hf
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let count : Polynomial Nat := q.comp (r.comp (Polynomial.C 2 * width))
  apply decideFlaggedSparse hv p bound count prune hp
  intro n xs hx
  have hwidth : width.eval n = 2*n + p.eval n + 1 := by simp [width]
  apply hprune (prefixExtension v) B fSpec (count.eval n) xs
  intro a ha zs hzs
  have hc : zs.card ≤ q.eval (r.eval (2 * width.eval n)) := by
    apply sparse _ zs
    intro y hy
    obtain ⟨hyB, w, hw, rfl⟩ := hzs y hy
    have ea := hx a ha
    have ew := hx w hw
    exact ⟨hyB, (hr a w).trans (eval_mono r (by omega))⟩
  simpa [count, Polynomial.eval_comp] using hc

/-- A cumulatively sparse target hard for coNP implies the reference P = NP. -/
theorem SparseCoHardImpliesCollapse (B : Language Bool)
    (hB : ∀ L ∈ coNP, PolyTimeReducible L B) (q : Polynomial Nat)
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
  exact decideCoSparse hv p hnorm B hB q sparse

end PEqualNP.Outside
