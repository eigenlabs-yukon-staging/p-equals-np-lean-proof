import PEqualNP.Outside.SparseCoHardImpliesCollapse
import PEqualNP.Outside.CoSparseQueryFrontier

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Verifier" => Word × Word → Bool

private theorem queryLength (qs : List Word) (z : Word) (hz : z ∈ qs) :
    z.length ≤ (encodeFrontier qs).length := by
  induction qs with
  | nil => simp at hz
  | cons x xs ih =>
    change z.length ≤ (pairB x (encodeFrontier xs)).length
    rw [pairB_length]
    rcases List.mem_cons.mp hz with rfl | hy
    · omega
    · have h := ih hy; omega

private theorem decideFromConjunctive {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (hb : ∀ x w : Word, v (x,w) = true → w.length ≤ p.eval x.length)
    (A B : Language Bool) (hA : ∀ L ∈ coNP, PolyTimeReducible L A)
    (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n)
    (queries : Word → List Word) (hf : CPT (fun x => encodeFrontier (queries x)))
    (spec : ∀ x : Word, x ∈ A ↔ ∀ y ∈ queries x, y ∈ B) :
    ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) ∈ P := by
  classical
  have hco : (prefixExtension v)ᶜ ∈ coNP := by
    change ((prefixExtension v)ᶜ)ᶜ ∈ NP
    rw [compl_compl]
    exact prefixExtension_np hv p hb
  obtain ⟨reduce, hreduce, reduceSpec⟩ := hA _ hco
  let qList := fun x : Word => queries (reduce x)
  let g := fun x : Word => encodeFrontier (qList x)
  have hg : CPT g := cpt_comp (g := fun x => encodeFrontier (queries x)) hreduce hf
  have qSpec (x : Word) : x ∈ prefixExtension v ↔ ∃ y ∈ qList x, y ∉ B := by
    have ht : x ∉ prefixExtension v ↔ ∀ y ∈ qList x, y ∈ B :=
      (reduceSpec x).trans (spec (reduce x))
    constructor
    · intro hm
      by_contra! hno
      exact (ht.mpr hno) hm
    · rintro ⟨y, hy, hno⟩
      by_contra h
      exact hno ((ht.mp h) y hy)
  obtain ⟨r, hr⟩ := output_length_poly g hg
  obtain ⟨prune, hp, hpSpec⟩ := CoSparseQueryFrontier qList hg
  let width : Polynomial Nat := Polynomial.C 2 * Polynomial.X + p + 1
  let bound := q.comp (r.comp width)
  apply decideFlaggedSparse hv p hb bound prune hp
  intro n xs hxs
  have ew : width.eval n = 2*n + p.eval n + 1 := by simp [width]
  have hcap (zs : Finset Word)
      (h : ∀ y ∈ zs, y ∈ B ∧ ∃ x ∈ xs, y ∈ qList x) : zs.card ≤ bound.eval n := by
    have h' : zs.card ≤ q.eval (r.eval (width.eval n)) := by
      apply sparse _ zs
      intro y hy
      obtain ⟨hyB,x,hx,hq⟩ := h y hy
      have hl := (queryLength (qList x) y hq).trans (hr x)
      exact ⟨hyB, hl.trans (eval_mono r ((hxs x hx).trans_eq ew.symm))⟩
    simpa [bound, Polynomial.eval_comp] using h'
  have hout := hpSpec (prefixExtension v) B qSpec (bound.eval n) xs hcap
  change
    (prune (pairB (un (bound.eval n)) (encodeFrontier xs)) = pairB [true] [] ∧
      ∃ x ∈ xs, x ∈ prefixExtension v) ∨
    (∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ bound.eval n ∧
      prune (pairB (un (bound.eval n)) (encodeFrontier xs)) = pairB [] (encodeFrontier ys) ∧
      ((∃ x ∈ ys, x ∈ prefixExtension v) ↔ ∃ x ∈ xs, x ∈ prefixExtension v)) at hout
  rcases hout with hy | ⟨ys, hs, hc, he, hmem⟩
  · exact Or.inl hy
  · exact Or.inr ⟨ys, hs, hc.trans (Nat.le_add_right _ _), he, hmem⟩

/-- A polynomial-time conjunctive reduction, with no fixed query-count cap, of a
pinned coNP-hard language to a sparse target implies the pinned P = NP. -/
theorem ConjunctiveCoSparseCollapse (A B : Language Bool)
    (hA : ∀ L ∈ coNP, PolyTimeReducible L A)
    (q : Polynomial Nat)
    (sparse : ∀ (n : Nat) (ys : Finset Word),
      (∀ y ∈ ys, y ∈ B ∧ y.length ≤ n) → ys.card ≤ q.eval n)
    (queries : Word → List Word)
    (hf : CPT (fun x =>
      (queries x).foldr (fun a b => List.replicate a.length true ++ false :: (a ++ b)) []))
    (spec : ∀ x : Word, x ∈ A ↔ ∀ y ∈ queries x, y ∈ B) :
    P = NP := by
  refine Set.Subset.antisymm L010 ?_
  intro L hL
  obtain ⟨R, p, ⟨v, hs, hv⟩, bound, he⟩ := L045 L hL
  have hn (x w : Word) (h : v (x,w) = true) : w.length ≤ p.eval x.length :=
    bound x w ((hs (x,w)).mpr h)
  have eq : L = ({x : Word | ∃ w : Word, v (x,w) = true} : Language Bool) :=
    Set.ext (fun x => (he x).trans (exists_congr (fun w => hs (x,w))))
  rw [eq]
  exact decideFromConjunctive hv p hn A B hA q sparse queries hf spec

end PEqualNP.Outside
