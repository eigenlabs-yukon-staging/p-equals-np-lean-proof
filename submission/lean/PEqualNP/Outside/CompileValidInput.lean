import PEqualNP.Library.Universal.Compile

/- The pinned compiler correctness proof with the valid input-stack invariant
   retained in its existential conclusion. Its simulation lemmas are unchanged. -/
namespace PEqualNP.Library.Universal
open Turing

variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
  (eOut : tm.Γ tm.k₁ ≃ Bool)

theorem compile_valid :
    ∃ (c : Code) (d : ℕ), c.kin < c.nstk ∧ ∀ (l : List (Bool ⊕ Bool)) (b : Bool) (n : ℕ),
      (flip bind (Turing.TM2.step tm.m))^[n] (some (Turing.initList tm (l.map eIn.invFun))) =
          some (Turing.haltList tm [eOut.invFun b]) →
      c.outputsWithin (l.map symIn) (d * n + d) [bitCode b] := by
  let E := envOf tm eIn eOut
  refine ⟨⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩,
    E.L.length + 3, E.numK_lt tm.k₀, fun l b n hrun => ?_⟩
  -- the initial configurations are related
  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y) (l.map symIn)
      (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have := E.decode_in (symIn_lt x)
    simpa [E, envOf, symOut_symIn] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map symIn)⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hpc, hst, hsr⟩ := E.sim_run n _ _ _ hrun hrel
  -- read off the final configuration
  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s, hs, hy⟩ : ∃ s, T.getD (E.numK tm.k₁) [] = [s] ∧
      E.decode tm.k₁ s = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOf]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin
  rw [hbit] at hT'
  refine Code.outputsWithin_mono _ _ (t := 3 + t) ?_ _ ?_
  · have : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold Code.outputsWithin Code.run Code.init
    simp only
    rw [hfin]
    exact ⟨rfl, hT'⟩

end PEqualNP.Library.Universal
