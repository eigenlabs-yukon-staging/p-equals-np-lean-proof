import PEqualNP.Outside.ParsimoniousCookLevin
import PEqualNP.Outside.MeasuredClauseSplit

open PEqualNP.Library PEqualNP.Search
open PEqualNP.Outside.CNFWidth (run run_cpt run_enc splitCNF split_width splitEquiv)
open PEqualNP.Library.Machines (cpt_comp)

theorem PEqualNP.Outside.ParsimoniousCookLevin3 :
    ∀ (v : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      ComputableInPolyTime encodePair Computability.encodeBool v →
      ∃ F : List Bool → CNF,
        ComputableInPolyTime (fun x : List Bool => x) (fun y : List Bool => y)
          (fun x => encodeCNF (F x)) ∧
        ∀ x : List Bool,
          let φ := F x
          IsKCNF 3 φ ∧
          Nonempty ({w : List Bool // w.length ≤ p.eval x.length ∧ v (x,w) = true} ≃
                    {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
                      CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                        then a ⟨i,h⟩ else false) φ = true}) := by
  intro v p hv
  obtain ⟨G,hG,hcorr⟩ := PEqualNP.Outside.ParsimoniousCookLevin v p hv
  refine ⟨fun x => splitCNF (G x),?_,?_⟩
  · have hf := cpt_comp hG run_cpt
    rw [show (fun x => run (encodeCNF (G x))) = (fun x => encodeCNF (splitCNF (G x))) from
      funext fun x => run_enc (G x) (hcorr x).1] at hf
    exact hf
  · intro x
    obtain ⟨hw,⟨he⟩⟩ := hcorr x
    exact ⟨split_width (G x) hw, ⟨he.trans (splitEquiv (G x))⟩⟩
