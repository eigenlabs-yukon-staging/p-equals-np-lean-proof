import PEqualNP.Outside.ParsimoniousTableau
import PEqualNP.Library.SearchHelpers.TableauStepCPT
import PEqualNP.Library.SearchHelpers.TableauEdgeCPT

namespace PEqualNP.Outside.OneHot
open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
open PEqualNP.Search PEqualNP.Library.SearchHelpers.Tab StepW

theorem pairs_cnfC (n : ℕ) (f : ℕ → List Bool → ℕ) (hf : ∀ i, VarC (f i)) :
    CnfC (fun s => pairs n (fun i => f i s)) := by
  unfold pairs
  apply cnfC_flatMap_const
  intro i
  apply cnfC_map_const
  intro j
  exact clC_cons (hf i) false (clC_cons (hf j) false clC_nil)

theorem row_cnfC (K B : ℕ) {H t : List Bool → ℕ}
    (hH : NatC H) (ht : NatC t) :
    CnfC (fun s =>
      pairs (B+1) (vP (t s)) ++ pairs B (vQ (t s)) ++
        (List.range K).flatMap fun k =>
          (List.range (H s)).flatMap fun j => pairs (B+1) (vC (t s) k j)) := by
  apply cnfC_append
  · apply cnfC_append
    · exact pairs_cnfC (B+1) _ (fun i => varC_vP ht (natC_const i))
    · exact pairs_cnfC B _ (fun i => varC_vQ ht (natC_const i))
  · apply cnfC_flatMap_const
    intro k
    apply cnfC_flatMap_range hH
    exact pairs_cnfC (B+1) _ (fun i => varC_vC (natC_snd ht) (natC_const k)
      natC_fst (natC_const i))

theorem strengthen_cnfC (K B : ℕ) {H T : List Bool → ℕ}
    (hH : NatC H) (hT : NatC T) : CnfC (fun s => strengthening K (H s) B (T s)) := by
  have h := cnfC_flatMap_range (natC_succ hT)
    (φ := fun t s =>
      pairs (B+1) (vP t) ++ pairs B (vQ t) ++
        (List.range K).flatMap fun k =>
          (List.range (H s)).flatMap fun j => pairs (B+1) (vC t k j))
    (row_cnfC K B (natC_snd hH) natC_fst)
  unfold CnfC at *
  apply Edge.cptE h
  intro s
  simp only [strengthening, groupVars, List.flatMap_assoc, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map]

def words (c : Universal.Code) (p q : Polynomial ℕ) (x : List Bool) : CNF :=
  formula c (x.map fun b => cond b 1 0) (p.eval x.length) (q.eval x.length)

theorem words_cnfC (c : Universal.Code) (p q : Polynomial ℕ) : CnfC (words c p q) := by
  unfold words formula
  apply cnfC_append
  · exact cpt_tableau_of c p q (cpt_stepPart c p q)
  · simp only [List.length_map]
    have hH : NatC (fun x => cellsOf x.length (p.eval x.length) (q.eval x.length)) := by
      refine Edge.cptE (natC_len (cpt_app2 cpt_id (cpt_app2 (L055 p)
        (cpt_app2 (L055 q) (cpt_const [true, true]))))) (fun x => ?_)
      congr 1
      simp only [cellsOf, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      omega
    exact strengthen_cnfC c.nstk (bound c) hH (L055 q)

end PEqualNP.Outside.OneHot

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Search

theorem PEqualNP.Outside.MeasuredParsimoniousTableau :
    ∀ (c : Code) (p q : Polynomial ℕ), c.kin < c.nstk →
      ∃ F : List Bool → CNF,
        ComputableInPolyTime (fun x : List Bool => x) (fun y : List Bool => y)
          (fun x => encodeCNF (F x)) ∧
        ∀ x : List Bool,
          let φ := F x
          Nonempty ({w : List Bool // w.length ≤ p.eval x.length ∧
                      c.outputsWithin ((x.map fun b => cond b 1 0) ++
                        w.map (fun b => cond b 3 2)) (q.eval x.length) [1]} ≃
                    {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
                      CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                        then a ⟨i,h⟩ else false) φ = true}) := by
  intro c p q hk
  refine ⟨PEqualNP.Outside.OneHot.words c p q, PEqualNP.Outside.OneHot.words_cnfC c p q, ?_⟩
  intro x
  refine ⟨PEqualNP.Outside.OneHot.models_equiv c _ _ _ ?_ hk⟩
  intro z hz
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hz
  cases b <;> decide
