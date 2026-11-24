import PEqualNP.Outside.FrontierExpansionMachine
import PEqualNP.Library.Machines.ReduceNP

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Map" => Word × Word → Word

private def parametrizedStep (g : Map) (s : Word) : Word :=
  let cap := (unpairB s).1
  let outer := (unpairB s).2
  let param := (unpairB outer).1
  let inner := (unpairB outer).2
  let todo := (unpairB inner).1
  let kept := (unpairB inner).2
  let q := g (param, (unpairB todo).1)
  let next := (unpairB todo).2
  let ok := bflag (decide (q.length ≤ cap.length))
  sel todo s (pairB cap (pairB param (pairB next (sel ok kept (kept ++ q)))))

private def paramMeasure (s : Word) : Nat := (unpairB s).1.length + 3

private theorem paramMeasure_step (g : Map) (s : Word) :
    paramMeasure (parametrizedStep g s) ≤ paramMeasure s := by
  unfold parametrizedStep
  dsimp only
  unfold sel
  split
  · exact le_rfl
  · simp [paramMeasure, unpairB_pairB]

private theorem paramStep_size (g : Map) (s : Word) :
    (parametrizedStep g s).length ≤ s.length + paramMeasure s := by
  have h₀ := unpairB_length s
  have h₁ := unpairB_length (unpairB s).2
  have h₂ := unpairB_length (unpairB (unpairB s).2).2
  have ht := unpairB_length (unpairB (unpairB (unpairB s).2).2).1
  unfold parametrizedStep paramMeasure
  dsimp only
  unfold sel
  split
  · omega
  · simp only [pairB_length]
    split
    · omega
    · rename_i h
      have hc := (not_congr (bflag_eq_nil _)).mp h
      simp only [Bool.not_eq_false, decide_eq_true_eq] at hc
      rw [List.length_append]
      omega

private theorem paramStep_cpt {g : Map}
    (hg : ComputableInPolyTime encodePair (fun x => x) g) : CPT (parametrizedStep g) := by
  have hc := cpt_unpairB1
  have houter := cpt_unpairB2
  have hp := cpt_unpairB1_1 houter
  have hi := cpt_unpairB2_1 houter
  have ht := cpt_unpairB1_1 hi
  have hk := cpt_unpairB2_1 hi
  have hx := cpt_unpairB1_1 ht
  have hq := cpt_comp (cpt_pair hp hx) hg
  have hf := cpt_bitFlag (cpt_comp (cpt_pair hc hq) LenCmp.lenLE_polyTime)
  exact bf_cptl (cpt_sel ht cpt_id (cpt_pairB2 hc (cpt_pairB2 hp (cpt_pairB2 (cpt_unpairB2_1 ht)
    (cpt_sel hf hk (cpt_app2 hk hq)))))) (fun _ => rfl)

private def paramState (cap p : Word) (todo kept : List Word) : Word :=
  pairB cap (pairB p (pairB (encodeFrontier todo) (encodeFrontier kept)))

private theorem paramRun_spec (g : Map) (children : Word × Word → List Word)
    (spec : ∀ p, g p = encodeFrontier (children p)) (cap p : Word) (xs : List Word) :
    ∀ n : Nat, xs.length ≤ n → ∀ acc : List Word,
      (∀ x ∈ xs, (g (p,x)).length ≤ cap.length) →
      (parametrizedStep g)^[n] (paramState cap p xs acc) =
        paramState cap p [] (acc ++ xs.flatMap (fun x => children (p,x))) := by
  induction xs with
  | nil =>
    intro n _ acc _
    have he : parametrizedStep g (paramState cap p [] acc) = paramState cap p [] acc := by
      simp [parametrizedStep, paramState, encodeFrontier, unpairB_pairB]
    simpa using Function.iterate_fixed he n
  | cons x xs ih =>
    intro n hn acc hcap
    cases n with
    | zero => simp at hn
    | succ n =>
      have hc : (encodeFrontier (children (p,x))).length ≤ cap.length := by
        simpa [spec] using hcap x List.mem_cons_self
      have hstep : parametrizedStep g (paramState cap p (x::xs) acc) =
          paramState cap p xs (acc ++ children (p,x)) := by
        have hne : pairB x (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne x xs
        change parametrizedStep g (pairB cap (pairB p (pairB (pairB x (encodeFrontier xs)) (encodeFrontier acc)))) = _
        simp [parametrizedStep, paramState, unpairB_pairB, sel, bflag, spec, hc, hne,
          encodeFrontier_append_words]
      rw [Function.iterate_succ_apply, hstep, ih n (by simpa using hn)]
      · simp [List.flatMap_cons, List.append_assoc]
      · exact fun y hy => hcap y (List.mem_cons_of_mem _ hy)

private def paramRaw (g : Map) (r : Polynomial Nat) (s : Word) : Word :=
  let cap := un (r.eval s.length)
  let init := pairB cap (pairB (unpairB s).1 (pairB (unpairB s).2 []))
  (unpairB (unpairB (unpairB ((parametrizedStep g)^[s.length] init)).2).2).2

private theorem paramRaw_cpt {g : Map}
    (hg : ComputableInPolyTime encodePair (fun x => x) g) (r : Polynomial Nat) :
    CPT (paramRaw g r) := by
  obtain ⟨c⟩ := paramStep_cpt hg
  have hi := cpt_pairB2 (L055 r) (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have h := Iter.iter_polyTime_measure (parametrizedStep g) c paramMeasure 3
    (paramMeasure_step g) (paramStep_size g) (fun s => by
      have hh := unpairB_length s
      unfold paramMeasure
      omega)
  have hv := cpt_comp (cpt_pair hi cpt_id) h
  exact bf_cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hv))) (fun _ => rfl)

private theorem word_in_frontier_size (xs : List Word) (x : Word) (hx : x ∈ xs) :
    x.length ≤ (encodeFrontier xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    change x.length ≤ (pairB y (encodeFrontier ys)).length
    rw [pairB_length]
    rcases List.mem_cons.mp hx with rfl | hm
    · omega
    · have h := ih hm
      omega

private theorem paramRaw_spec (g : Map) (children : Word × Word → List Word)
    (spec : ∀ p, g p = encodeFrontier (children p))
    (r : Polynomial Nat) (bound : ∀ s, (g (unpairB s)).length ≤ r.eval (List.length s))
    (p : Word) (xs : List Word) :
    paramRaw g r (pairB p (encodeFrontier xs)) =
      encodeFrontier (xs.flatMap (fun x => children (p,x))) := by
  let s := pairB p (encodeFrontier xs)
  let cap := un (r.eval s.length)
  have hn : xs.length ≤ s.length := by
    have := encodeFrontier_length xs
    simp only [s, pairB_length]
    omega
  have hc (x : Word) (hx : x ∈ xs) : (g (p,x)).length ≤ cap.length := by
    have ht := bound (pairB p x)
    rw [unpairB_pairB] at ht
    have hs : (pairB p x).length ≤ s.length := by
      have h := word_in_frontier_size xs x hx
      simp only [s, pairB_length]
      omega
    simpa [cap, un_length] using ht.trans (eval_mono r hs)
  have he := paramRun_spec g children spec cap p xs s.length hn [] hc
  change paramRaw g r s = _
  unfold paramRaw
  simp only [s, unpairB_pairB]
  change (unpairB (unpairB (unpairB ((parametrizedStep g)^[s.length]
    (paramState cap p xs []))).2).2).2 = _
  rw [he]
  simp [paramState, unpairB_pairB]

/-- A tagged-pair polynomial-time child generator can be mapped over an encoded
list with a single common parameter. -/
theorem ParameterizedFrontierExpansion (children : Word × Word → List Word)
    (hg : ComputableInPolyTime encodePair (fun x => x) (fun p =>
      (children p).foldr (fun a b => List.replicate a.length true ++ false :: (a ++ b)) [])) :
    ∃ run : Word × Word → Word, ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (p : Word) (xs : List Word),
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (p, xs.foldr consWord []) = (xs.flatMap (fun x => children (p,x))).foldr consWord [] := by
  let g := fun p => encodeFrontier (children p)
  obtain ⟨r, hr⟩ := output_length_poly (fun s => g (unpairB s)) (cpt_comp cpt_unpairB hg)
  exact ⟨fun p => paramRaw g r (pairB p.1 p.2), cpt_comp cpt_pairB (paramRaw_cpt hg r),
    paramRaw_spec g children (fun _ => rfl) r hr⟩

end PEqualNP.Outside
