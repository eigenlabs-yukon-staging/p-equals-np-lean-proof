import PEqualNP.Outside.OptimalCostWitnessSearch
import PEqualNP.Library.Machines.ReduceNP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside (OptimalCostWitnessSearch P_subset_NP CollapseFromWitnessSearch)

private theorem cost_bound (p : Polynomial ℕ) (cost : List Bool × List Bool → List Bool)
    (hc : ComputableInPolyTime encodePair (fun x : List Bool => x) cost) :
    ∃ r : Polynomial ℕ, ∀ x w, w.length ≤ p.eval x.length →
      (cost (x, w)).length ≤ r.eval x.length := by
  let f := fun z : List Bool => cost (unpairB z)
  have hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f :=
    cpt_comp cpt_unpairB hc
  obtain ⟨q, hq⟩ := output_length_poly f hf
  refine ⟨q.comp (Polynomial.C 2 * Polynomial.X + p + 1), ?_⟩
  intro x w h
  have hm := hq (pairB x w)
  simp only [f, unpairB_pairB, pairB_length] at hm
  refine hm.trans ?_
  rw [Polynomial.eval_comp]
  apply PEqualNP.Outside.PrefixDecideHelpers.eval_mono_nat
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

theorem PEqualNP.Outside.OptimalCostWitnessSearchAutoBound :
    P = NP ↔
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
      (cost : List Bool × List Bool → List Bool),
      DecidableInPolyTime encodePair R →
      ComputableInPolyTime encodePair (fun x : List Bool => x) cost →
      ∃ select : List Bool → List Bool,
        ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) select ∧
        ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R) →
          (select x).length ≤ p.eval x.length ∧ (x, select x) ∈ R ∧
          ∀ v : List Bool, v.length ≤ p.eval x.length → (x, v) ∈ R →
            (cost (x, select x)).length < (cost (x, v)).length ∨
            (cost (x, select x)).length = (cost (x, v)).length ∧
              (cost (x, select x) = cost (x, v) ∨
                List.Lex (fun a b => a = false ∧ b = true) (cost (x, select x)) (cost (x, v))) := by
  constructor
  · intro he R p cost hR hc
    obtain ⟨r, hr⟩ := cost_bound p cost hc
    exact (OptimalCostWitnessSearch.mp he) R p r cost hR hc (fun x w h _ => hr x w h)
  · intro h
    apply OptimalCostWitnessSearch.mpr
    intro R p r cost hR hc _
    exact h R p cost hR hc
