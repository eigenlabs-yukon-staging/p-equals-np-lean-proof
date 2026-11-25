import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Outside.MeasuredClauseLiteralCount

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.Search

private def step (split : List Bool → List Bool × List Bool)
    (count : List Bool → List Bool) (s : List Bool) : List Bool :=
  let rest := (unpairB s).1
  let cap := (unpairB (unpairB s).2).1
  let acc := (unpairB (unpairB s).2).2
  if rest = [] then s
  else pairB (split rest).2 (pairB cap (tk cap (mulU (count (split rest).1) acc)))

private theorem step_cpt
    {split : List Bool → List Bool × List Bool} {count : List Bool → List Bool}
    (hs : ComputableInPolyTime (fun x : List Bool => x) encodePair split)
    (hc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) count) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step split count) := by
  have hr := cpt_unpairB1
  have hp := cpt_unpairB1_1 cpt_unpairB2
  have ha := cpt_unpairB2_1 cpt_unpairB2
  have hpair := cpt_comp hr hs
  have hwidth := cpt_comp (cpt_comp hpair cpt_fst) hc
  have htail := cpt_comp hpair cpt_snd
  exact cpt_sel hr cpt_id (cpt_pairB2 htail (cpt_pairB2 hp (cpt_tk hp (cpt_mulU2 hwidth ha))))

private def measure (s : List Bool) : ℕ := (unpairB (unpairB s).2).1.length + 2

private theorem measure_step (split : List Bool → List Bool × List Bool) (count : List Bool → List Bool)
    (s : List Bool) : measure (step split count s) ≤ measure s := by
  dsimp only [step]
  split
  · rfl
  · simp [measure, unpairB_pairB]

private theorem step_length
    {split : List Bool → List Bool × List Bool} {count : List Bool → List Bool}
    (hj : ∀ x, (split x).1 ++ (split x).2 = x) (s : List Bool) :
    (step split count s).length ≤ s.length + measure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := congrArg List.length (hj (unpairB s).1)
  have ht := tk_length (unpairB (unpairB s).2).1
    (mulU (count (split (unpairB s).1).1) (unpairB (unpairB s).2).2)
  simp only [List.length_append] at h3
  dsimp only [step, measure]
  split
  · omega
  · simp only [pairB_length]
    omega

private theorem measure_bound (s : List Bool) : measure s ≤ 2 * s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  unfold measure
  omega

private theorem prod_clip (cap n m : ℕ) :
    min cap (n * min cap m) = min cap (n*m) := by
  by_cases hm : m ≤ cap
  · rw [Nat.min_eq_right hm]
  · have hcap : cap ≤ m := by omega
    rw [Nat.min_eq_left hcap]
    cases n with
    | zero => simp
    | succ n =>
        have hn : 1 ≤ n+1 := by omega
        have h1 := Nat.mul_le_mul_right cap hn
        have h2 := Nat.mul_le_mul_right m hn
        have h1' : cap ≤ (n+1)*cap := by simpa using h1
        have h2' : cap ≤ (n+1)*m := hcap.trans (by simpa using h2)
        rw [Nat.min_eq_left h1', Nat.min_eq_left h2']

private theorem fold_clip (cap n m : ℕ) : min cap (min cap m * n) = min cap (m*n) := by
  rw [Nat.mul_comm (min cap m) n, Nat.mul_comm m n, prod_clip]

private theorem encode_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]

private theorem run
    {split : List Bool → List Bool × List Bool}
    {count : List Bool → List Bool}
    (hs : ∀ c r, split (encodeClause c ++ r) = (encodeClause c,r))
    (hc : ∀ c, count (encodeClause c) = List.replicate c.length true)
    (φ : CNF) (cap acc : List Bool) (n : ℕ) (hn : φ.length ≤ n)
    (hacc : acc.length ≤ cap.length) :
    (unpairB (unpairB ((step split count)^[n] (pairB (encodeCNF φ) (pairB cap acc)))).2).2.length =
      min cap.length (acc.length * (φ.map List.length).prod) := by
  induction n generalizing φ acc with
  | zero =>
      have hnil : φ = [] := List.length_eq_zero_iff.mp (by omega)
      subst φ
      simp [unpairB_pairB, Nat.min_eq_right hacc]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases φ with
      | nil =>
          have e : step split count (pairB (encodeCNF []) (pairB cap acc)) =
              pairB (encodeCNF []) (pairB cap acc) := by simp [step, unpairB_pairB, encodeCNF]
          rw [e, ih [] _ (by simp) hacc]
      | cons c φ =>
          have hne : encodeClause c ++ encodeCNF φ ≠ [] := by simp [encodeClause]
          have htail : φ.length ≤ n := by simpa using hn
          rw [encode_cons]
          simp only [step,unpairB_pairB,hs,hc,ite_eq_right hne]
          rw [ih φ _ htail (tk_length _ _), tk_eq, List.length_take]
          have hm : (mulU (List.replicate c.length true) acc).length = c.length*acc.length := by
            simp [mulU, un]
          rw [hm, fold_clip, List.map_cons, List.prod_cons]
          ac_rfl

private theorem formula_length (φ : CNF) : φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.length_cons, encode_cons, List.length_append]
      have h : 1 ≤ (encodeClause c).length := by simp [encodeClause]
      omega

/-- The product of canonical clause widths, clipped at a unary cap, is measured
in polynomial time without storing an oversized product. -/
theorem MeasuredCappedClauseProduct :
    ∃ product : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) product ∧
      ∀ (φ : CNF) (cap : List Bool),
        (product (cap,encodeCNF φ)).length = min cap.length ((φ.map List.length).prod) := by
  obtain ⟨split,hs,hj,hcs⟩ := measuredFirstClause_reassembles
  obtain ⟨count,hc,hcc⟩ := MeasuredClauseLiteralCount
  let init := fun s => pairB (unpairB s).2 (pairB (unpairB s).1 (tk (unpairB s).1 [true]))
  let loop := fun s => (step split count)^[(unpairB s).2.length] (init s)
  let get := fun s => (unpairB (unpairB (loop s)).2).2
  have hi := cpt_pairB2 cpt_unpairB2
    (cpt_pairB2 cpt_unpairB1 (cpt_tk cpt_unpairB1 (cpt_const [true])))
  have hl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) loop :=
    cpt_iterMeasure (step_cpt hs hc) measure 2 (measure_step split count)
      (step_length hj) measure_bound cpt_unpairB2 hi
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) get :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hl)
  refine ⟨fun p => get (pairB p.1 p.2), cpt_comp (g := get) cpt_pairB hg, fun φ cap => ?_⟩
  simp only [get,loop,init,unpairB_pairB]
  rw [run hcs hcc _ _ _ _ (formula_length φ) (tk_length _ _)]
  nth_rw 1 [show (tk cap [true]).length = min cap.length 1 by
    rw [tk_eq, List.length_take, List.length_singleton]]
  rw [fold_clip, Nat.one_mul]

end PEqualNP.Outside
