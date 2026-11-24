import PEqualNP.Outside.FixedCoinTapeQueryIsolation
import PEqualNP.Outside.PromiseOracleSimulationMachine

open PEqualNP.Library
open PEqualNP.Outside.PromiseOracleSimulationMachine
  (simulate simulate_cpt batch_correct wrong_length coinPolynomial coinPolynomial_eval)

theorem PEqualNP.Outside.PromiseOracleOneSidedSimulation :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (p : Polynomial ℕ) (D : List Bool × List Bool → Bool) (K : Language Bool),
        K ∈ NP ∧ ComputableInPolyTime encodePair Computability.encodeBool D ∧
        (∀ z, z ∈ K ↔ ∃ w, D (z,w) = true) ∧
        ∀ O : List Bool → Bool,
          ComputableInPolyTime (fun w : List Bool => w) Computability.encodeBool O →
          (∀ z, (∀ w, D (z,w) = false) → O z = false) →
          (∀ z, (∃! w, D (z,w) = true) → O z = true) →
          ∃ F : List Bool × List Bool → Bool,
            ComputableInPolyTime encodePair Computability.encodeBool F ∧
            (∀ x ∉ L, ∀ r : List Bool, F (x,r) = false) ∧
            ∀ x ∈ L,
              let b := p.eval x.length
              let n := (2*b+3) * (2*b+2)
              Fintype.card (Fin n → Bool) ≤ 8 *
                ((Finset.univ : Finset (Fin n → Bool)).filter
                  (fun u => F (x, List.ofFn u) = true)).card := by
  intro L hL
  obtain ⟨p,W,Q,G,D,K,hK,hD,hG,hquery,hw,hgenerate,hsound,hgood⟩ :=
    PEqualNP.Outside.FixedCoinTapeQueryIsolation L hL
  refine ⟨p,D,K,hK,hD,hquery,?_⟩
  intro O hO hzero hone
  let F := simulate p G O
  have ht (x : List Bool)
      (u : Fin ((2 * p.eval x.length + 3) * (2 * p.eval x.length + 2)) → Bool) :
      F (x, List.ofFn u) = true ↔ ∃ z ∈ Q x u, O z = true := by
    exact batch_correct p G O x (List.ofFn u) (Q x u)
      (by rw [coinPolynomial_eval, List.length_ofFn]) (hgenerate x u)
  refine ⟨F, simulate_cpt p G O hG hO, ?_, ?_⟩
  · intro x hx r
    by_cases hlen : r.length = (coinPolynomial p).eval x.length
    · let n := (2 * p.eval x.length + 3) * (2 * p.eval x.length + 2)
      have hn : r.length = n := hlen.trans (coinPolynomial_eval _ _)
      let u (i : Fin n) := r[i.val]'(by rw [hn]; exact i.isLt)
      have e : List.ofFn u = r := by
        apply List.ext_getElem
        · rw [List.length_ofFn, ← hn]
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn, u]
      rw [← e]
      cases h : F (x,List.ofFn u)
      · rfl
      · obtain ⟨z,hz,ho⟩ := (ht x u).mp h
        have hno (w : List Bool) : D (z,w) = false := by
          cases hd : D (z,w)
          · rfl
          · exact False.elim (hx ((hw x).mpr ⟨w, hsound x u z hz w hd⟩))
        rw [hzero z hno] at ho
        contradiction
    · exact wrong_length p G O x r hlen
  · intro x hx
    have hg := hgood x hx
    refine hg.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card ?_))
    intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    obtain ⟨hm,z,hz,w,hw',htrue,huniq⟩ := hu
    have hz' := List.mem_toFinset.mp hz
    refine ⟨hm, (ht x u).mpr ⟨z, hz', hone z ?_⟩⟩
    refine ⟨w,htrue,?_⟩
    intro v hv
    by_contra hne
    rw [huniq v (hsound x u z hz' v hv) hne] at hv
    contradiction
