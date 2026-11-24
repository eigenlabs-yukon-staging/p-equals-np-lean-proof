import PEqualNP.Outside.MeasuredSparseConjunctiveBoundary
import PEqualNP.Outside.LexPrefixQueryNP
import PEqualNP.Outside.ExactWitnessPadding
import PEqualNP.Outside.BoundedConjunctiveSparseCollapse
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open SparseFrontierSupport

local notation "Word" => List Bool
local notation "Verifier" => Word × Word → Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "ltBit" => (fun a b : Bool => !a && b)

private theorem lex_not_gt (a b : Word) : a.lex b ltBit = false ↔ b ≤ a := by
  have e : ltBit = (fun x y : Bool => decide (x < y)) := by
    funext x y
    cases x <;> cases y <;> rfl
  rw [e]
  have ht := List.lex_eq_true_iff_lt (l₁ := a) (l₂ := b)
  constructor
  · intro h
    apply le_of_not_gt
    intro hn
    have hh := ht.mpr hn
    rw [h] at hh
    contradiction
  · intro h
    cases he : a.lex b (fun x y => decide (x < y))
    · rfl
    · exact False.elim ((not_lt_of_ge h) (ht.mp he))

private theorem take_mono_equal (a b : Word) (h : a ≤ b) (hlen : a.length = b.length) (k : Nat) :
    a.take k ≤ b.take k := by
  by_contra hn
  have hlt : b.take k < a.take k := lt_of_not_ge hn
  have hl : (b.take k).length = (a.take k).length := by simp [hlen]
  have hc : b.take k ++ b.drop k < a.take k ++ a.drop k :=
    (List.append_lt_append_iff_of_length_eq hl).mpr (Or.inl hlt)
  have hh : b < a := by simpa using hc
  exact (not_lt_of_ge h) hh

private def reverseChildren (s : Word) : List Word :=
  let p := unpairB s
  [pairB p.1 (p.2 ++ [true]), pairB p.1 (p.2 ++ [false])]

private theorem reverseChildren_cpt : CPT (fun s => encodeFrontier (reverseChildren s)) := by
  have ht := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [true]))
  have hf := cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 (cpt_const [false]))
  exact cpt_pairB2 ht (cpt_pairB2 hf (cpt_const []))

private def prefixLt (a b : Word) : Prop := (unpairB a).2 < (unpairB b).2

private def depthFront (x : Word) (k : Nat) (xs : List Word) : Prop :=
  xs.Pairwise (fun a b => prefixLt b a) ∧
    ∀ y ∈ xs, ∃ w : Word, y = pairB x w ∧ w.length = k

private theorem children_of (x w : Word) :
    reverseChildren (pairB x w) = [pairB x (w ++ [true]), pairB x (w ++ [false])] := by
  simp [reverseChildren, unpairB_pairB]

private theorem child_at_depth (x : Word) (k : Nat) (u v : Word)
    (hu : ∃ w : Word, u = pairB x w ∧ w.length = k) (hv : v ∈ reverseChildren u) :
    ∃ w : Word, v = pairB x w ∧ w.length = k + 1 := by
  obtain ⟨w,rfl,hw⟩ := hu
  rw [children_of] at hv
  have h : v = pairB x (w ++ [true]) ∨ v = pairB x (w ++ [false]) := by simpa using hv
  rcases h with rfl | rfl
  · exact ⟨w ++ [true], rfl, by simp [hw]⟩
  · exact ⟨w ++ [false], rfl, by simp [hw]⟩

private theorem reverseChildren_order (x : Word) (k : Nat) (xs : List Word)
    (h : depthFront x k xs) : depthFront x (k+1) (xs.flatMap reverseChildren) := by
  obtain ⟨sorted, hxs⟩ := h
  constructor
  · rw [List.pairwise_flatMap]
    constructor
    · intro y hy
      obtain ⟨w,rfl,_⟩ := hxs y hy
      rw [children_of]
      have hbit : ([false] : Word) < [true] := List.Lex.rel (by decide : false < true)
      simp [prefixLt, unpairB_pairB, hbit]
    · apply sorted.imp_of_mem
      intro a b ha hb hab u hu v hv
      obtain ⟨wa, rfl, hwa⟩ := hxs a ha
      obtain ⟨wb, rfl, hwb⟩ := hxs b hb
      have hlt : wb < wa := by simpa [prefixLt, unpairB_pairB] using hab
      rw [children_of] at hu hv
      have hu' : u = pairB x (wa++[true]) ∨ u = pairB x (wa++[false]) := by simpa using hu
      have hv' : v = pairB x (wb++[true]) ∨ v = pairB x (wb++[false]) := by simpa using hv
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;>
        simp [prefixLt, unpairB_pairB, List.append_lt_append_iff_of_length_eq (hwb.trans hwa.symm), hlt]
  · intro z hz
    obtain ⟨y,hy,hmem⟩ := List.mem_flatMap.mp hz
    exact child_at_depth x k y z (hxs y hy) hmem

private theorem depthFront_sublist {x : Word} {k : Nat} {xs ys : List Word}
    (h : depthFront x k xs) (hs : ys.Sublist xs) : depthFront x k ys :=
  ⟨h.1.sublist hs, fun y hy => h.2 y (hs.subset hy)⟩

private theorem cover_minimum {v : Verifier} (x : Word) (n : Nat)
    (len : ∀ w, v (x,w) = true → w.length = n)
    (w : Word) (hw : v (x,w) = true) (hmin : ∀ y, v (x,y) = true → w ≤ y)
    (k : Nat) (_hk : k ≤ n) (t : Word) (ht : t.length = k) :
    pairB x t ∈ lexPrefixQuery v ↔ w.take k ≤ t := by
  rw [lexPrefixQuery_pair]
  constructor
  · rintro ⟨y,hy,h⟩
    have hs : w.take k ≤ y.take k := take_mono_equal w y (hmin y hy) ((len w hw).trans (len y hy).symm) k
    exact hs.trans (lex_not_gt t _ |>.mp (by simpa [ht] using h))
  · intro h
    exact ⟨w, hw, (lex_not_gt t _).mpr (by simpa [ht] using h)⟩

private theorem leastWitness (v : Verifier) (x : Word) (n : Nat)
    (len : ∀ w, v (x,w) = true → w.length = n)
    (yes : ∃ w, v (x,w) = true) :
    ∃ w, v (x,w) = true ∧ ∀ u, v (x,u) = true → w ≤ u := by
  let B : Language Bool := {w | v (x,w) = true}
  let s := acceptedShort B n
  have hmem (w : Word) (hw : v (x,w) = true) : w ∈ s :=
    mem_acceptedShort B n w hw (len w hw).le
  have hs : s.Nonempty := by
    obtain ⟨w,hw⟩ := yes
    exact ⟨w,hmem w hw⟩
  exact ⟨s.min' hs, (acceptedShort_spec B n _ (s.min'_mem hs)).1,
    fun u hu => s.min'_le u (hmem u hu)⟩

private theorem query_member_length (qs : List Word) (z : Word) (hz : z ∈ qs) :
    z.length ≤ (encodeFrontier qs).length := by
  induction qs with
  | nil => simp at hz
  | cons x xs ih =>
    change z.length ≤ (pairB x (encodeFrontier xs)).length
    rw [pairB_length]
    rcases List.mem_cons.mp hz with rfl | hy
    · omega
    · have h := ih hy; omega

private theorem decideConjunctive {v : Verifier} (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (bound : ∀ x w : Word, v (x,w) = true → w.length = p.eval x.length)
    (A B : Language Bool) (hA : NPHard A) (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n)
    (queries : Word → List Word) (hf : CPT (fun x => encodeFrontier (queries x)))
    (relation : ∀ x : Word, x ∈ A ↔ ∀ y ∈ queries x, y ∈ B) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  classical
  obtain ⟨reduce, hreduce, rSpec⟩ := hA _ (lexPrefixQuery_np hv p
    (fun x w hw => (bound x w hw).le))
  let qs := fun s : Word => queries (reduce s)
  let g := fun s : Word => encodeFrontier (qs s)
  have hg : CPT g := cpt_comp (g := fun x => encodeFrontier (queries x)) hreduce hf
  have qSpec (s : Word) : s ∈ lexPrefixQuery v ↔ ∀ y ∈ qs s, y ∈ B :=
    (rSpec s).trans (relation (reduce s))
  obtain ⟨r, hr⟩ := output_length_poly g hg
  obtain ⟨prune, hpruneCpt, keep, keepSpec, keepBoundary⟩ :=
    MeasuredSparseConjunctiveBoundary qs hg
  let ch := fun s => encodeFrontier (reverseChildren s)
  obtain ⟨a, H⟩ := output_length_poly ch reverseChildren_cpt
  let expand := expandFrontier ch a
  have hexpand : CPT expand := expandFrontier_polyTime reverseChildren_cpt a
  have exSpec (xs : List Word) : expand (encodeFrontier xs) =
      encodeFrontier (xs.flatMap reverseChildren) :=
    expandFrontier_spec reverseChildren ch (fun _ => rfl) a H xs
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let count : Polynomial Nat := q.comp (r.comp width)
  let cap : Polynomial Nat := (Polynomial.C 2 * width + 1) * (count + Polynomial.C 2)
  let state := fun (x : Word) (xs : List Word) => pairB (un (cap.eval x.length))
    (pairB (un (count.eval x.length)) (encodeFrontier xs))
  let initial := fun x : Word => state x [pairB x []]
  have hinitial : CPT initial :=
    cpt_pairB2 (L055 cap) (cpt_pairB2 (L055 count)
      (cpt_pairB2 (cpt_pairB2 cpt_id (cpt_const [])) (cpt_const [])))
  let run := fun x : Word => (boundedStep expand prune)^[p.eval x.length] (initial x)
  have hrun : CPT run :=
    bf_cptl (boundedIter_cpt hexpand hpruneCpt hinitial (L055 p)) (fun x => by simp [run])
  let dec := fun x : Word => leafTest v ((unpairB (unpairB (run x)).2).2)
  have hdec : ComputableInPolyTime (fun x => x) Computability.encodeBool dec :=
    cpt_comp (cpt_unpairB2_1 (cpt_unpairB2_1 hrun)) (leafTest_cpt hv)
  refine ⟨dec, fun x => ?_, hdec⟩
  have wSpec : width.eval x.length = 2*x.length + p.eval x.length + 1 := by simp [width]
  have capSpec : cap.eval x.length =
      (2 * width.eval x.length + 1) * (count.eval x.length + 2) := by simp [cap]
  let S := acceptedShort B (r.eval (width.eval x.length))
  have hS : S.card ≤ count.eval x.length := by
    have h := sparse _ S (acceptedShort_spec B _)
    simpa [count, Polynomial.eval_comp] using h
  have inv (k : Nat) (hk : k ≤ p.eval x.length) :
      ∃ xs : List Word,
        (boundedStep expand prune)^[k] (initial x) = state x xs ∧
        depthFront x k xs ∧
        ∀ w : Word, v (x,w) = true → (∀ u, v (x,u) = true → w ≤ u) →
          pairB x (w.take k) ∈ xs := by
    induction k with
    | zero =>
      refine ⟨[pairB x []], rfl, ?_, by simp⟩
      refine ⟨by simp, fun y hy => ⟨[], by simpa using hy, rfl⟩⟩
    | succ k ih =>
      obtain ⟨xs, hstate, hd, hmin⟩ := ih (by omega)
      let zs := xs.flatMap reverseChildren
      have hz : depthFront x (k+1) zs := reverseChildren_order x k xs hd
      have hlen (y : Word) (hy : y ∈ zs) : y.length ≤ width.eval x.length := by
        obtain ⟨w, rfl, hw⟩ := hz.2 y hy
        rw [pairB_length, wSpec, hw]
        omega
      let ys := keep (count.eval x.length) zs
      have hs := keepSpec (count.eval x.length) zs
      change prune (pairB (un (count.eval x.length)) (encodeFrontier zs)) = encodeFrontier ys ∧
        ys.Sublist zs ∧ ys.length ≤ count.eval x.length + 2 at hs
      obtain ⟨hout, hsub, hsize⟩ := hs
      have hcap : (encodeFrontier ys).length ≤ cap.eval x.length := by
        rw [capSpec]
        exact (frontierSize _ ys (fun y hy => hlen y (hsub.subset hy))).trans
          (Nat.mul_le_mul_left _ hsize)
      have hstep : boundedStep expand prune (state x xs) = state x ys := by
        have ex : expand (encodeFrontier xs) = encodeFrontier zs := exSpec xs
        simp [boundedStep, state, unpairB_pairB, ex, hout, bflag, hcap, un_length]
      refine ⟨ys, ?_, depthFront_sublist hz hsub, fun w hw hleast => ?_⟩
      · rw [Function.iterate_succ_apply', hstate, hstep]
      let c := pairB x (w.take (k+1))
      have hc : c ∈ zs := by
        have hlt : k < w.length := by rw [bound x w hw]; omega
        apply List.mem_flatMap.mpr
        refine ⟨pairB x (w.take k), hmin w hw hleast, ?_⟩
        rw [children_of]
        dsimp [c]
        rw [List.take_succ_eq_append_getElem hlt]
        cases w[k] <;> simp
      obtain ⟨left, right, hsplit⟩ := List.append_of_mem hc
      have sorted : (left ++ c :: right).Pairwise (fun a b => prefixLt b a) :=
        hsplit ▸ hz.1
      have H := List.pairwise_append.mp sorted
      have htrue : ∀ y ∈ left ++ [c], ∀ t ∈ qs y, t ∈ S := by
        intro y hy t ht
        have hym : y ∈ zs := by
          rw [hsplit]
          simpa only [List.append_assoc, List.singleton_append] using List.mem_append_left right hy
        obtain ⟨u, hu, hlenU⟩ := hz.2 y hym
        have hge : w.take (k+1) ≤ u := by
          rcases List.mem_append.mp hy with hl | he
          · have hlt := H.2.2 y hl c List.mem_cons_self
            exact le_of_lt (by simpa [prefixLt, c, hu, unpairB_pairB] using hlt)
          · have eq : y = c := List.mem_singleton.mp he
            have hp := congrArg (fun q => (unpairB q).2) (hu.symm.trans eq)
            simp [c, unpairB_pairB] at hp
            exact le_of_eq hp.symm
        have hmem : y ∈ lexPrefixQuery v := hu ▸
          (cover_minimum x (p.eval x.length) (bound x) w hw hleast (k+1) hk u hlenU).mpr hge
        have hB := (qSpec y).mp hmem t ht
        have hquery := (query_member_length (qs y) t ht).trans (hr y)
        exact mem_acceptedShort B _ t hB (hquery.trans (eval_mono r (hlen y hym)))
      have hrest : right = [] ∨ ∃ y ys, right = y :: ys ∧ ∃ t ∈ qs y, t ∉ S := by
        cases right with
        | nil => exact Or.inl rfl
        | cons t ts =>
          right
          refine ⟨t,ts,rfl,?_⟩
          have htm : t ∈ zs := by rw [hsplit]; simp
          obtain ⟨u,hu,hlenU⟩ := hz.2 t htm
          have hlt : u < w.take (k+1) := by
            have h := (List.pairwise_cons.mp H.2.1).1 t List.mem_cons_self
            simpa [prefixLt, hu, c, unpairB_pairB] using h
          have hn : t ∉ lexPrefixQuery v := by
            rw [hu, cover_minimum x (p.eval x.length) (bound x) w hw hleast (k+1) hk u hlenU]
            exact not_le_of_gt hlt
          have hco : ¬∀ z ∈ qs t, z ∈ B := (qSpec t).not.mp hn
          push Not at hco
          obtain ⟨z,hz,hzB⟩ := hco
          exact ⟨z,hz,fun h => hzB (acceptedShort_spec B _ z h).1⟩
      have hk' := keepBoundary (count.eval x.length) S hS left right c htrue hrest
      change c ∈ ys
      simpa [ys, hsplit, List.append_assoc] using hk'
  obtain ⟨xs, hstate, hd, hm⟩ := inv (p.eval x.length) le_rfl
  change (∃ w : Word, v (x,w) = true) ↔ dec x = true
  have hex : dec x = leafTest v (encodeFrontier xs) := by
    simp only [dec, run, hstate, state, unpairB_pairB]
  rw [hex, leafTest_spec]
  constructor
  · intro yes
    obtain ⟨w,hw,hmin⟩ := leastWitness v x (p.eval x.length) (bound x) yes
    have h := hm w hw hmin
    rw [← bound x w hw, List.take_length] at h
    exact ⟨pairB x w,h,by simpa [unpairB_pairB] using hw⟩
  · rintro ⟨y,hy,hv⟩
    obtain ⟨w,rfl,_⟩ := hd.2 y hy
    exact ⟨w, by simpa [unpairB_pairB] using hv⟩

/-- A conjunctive reduction of a pinned NP-hard language to a cumulatively sparse
language implies the pinned equality, with no fixed limit on the query count. -/
theorem ConjunctiveSparseCollapse (A B : Language Bool) (hA : NPHard A)
    (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n)
    (queries : Word → List Word)
    (hf : CPT (fun x => (queries x).foldr
      (fun a b => List.replicate a.length true ++ false :: (a ++ b)) []))
    (relation : ∀ x : Word, x ∈ A ↔ ∀ y ∈ queries x, y ∈ B) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro L hL
  obtain ⟨R, p, ⟨v,spec,hv⟩, b, hspec⟩ := ExactWitnessPadding L hL
  have hbound (x w : Word) (h : v (x,w) = true) : w.length = p.eval x.length :=
    b x w ((spec (x,w)).mpr h)
  have e : L = ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) :=
    Set.ext (fun x => (hspec x).trans (exists_congr (fun w => spec (x,w))))
  rw [e]
  exact decideConjunctive hv p hbound A B hA q sparse queries hf relation

end PEqualNP.Outside
