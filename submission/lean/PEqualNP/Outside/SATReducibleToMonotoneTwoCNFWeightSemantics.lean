import PEqualNP.Outside.MonotoneTwoCNFWeightReduction

open PEqualNP.Search PEqualNP.Outside.ClauseOccurrenceConflict
open PEqualNP.Outside.MonotoneTwoCNFWeightReduction

theorem PEqualNP.Outside.SATReducibleToMonotoneTwoCNFWeightSemantics :
    ∀ φ : CNF,
      ∃ ψ : CNF, ∃ k : ℕ,
        k = (φ.map List.length).sum + 1 ∧
        (∀ c ∈ ψ, c.length ≤ 2 ∧ c.all Prod.snd = true) ∧
        (Satisfiable φ ↔ ∃ σ : Assignment, CNF.eval σ ψ = true ∧
          ((ψ.flatMap fun c => c.map Prod.fst).toFinset.filter (fun i => σ i = true)).card ≤ k) := by
  intro φ
  classical
  let t : Occurrence φ ↪ ℕ := (Fintype.equivFin (Occurrence φ)).toEmbedding.trans
    ⟨Fin.val, Fin.val_injective⟩
  have hcard : Fintype.card (Occurrence φ) = (φ.map List.length).sum := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← List.sum_ofFn]
    congr
    apply List.ext_getElem
    · simp
    · intro n hn₁ hn₂
      simp
  exact ⟨graphCNF t, Fintype.card (Occurrence φ) + 1, by rw [hcard],
    graph_shape t, (weight_iff_sat φ t).symm⟩
