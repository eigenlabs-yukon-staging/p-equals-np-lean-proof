import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

private def nextPrefix (accept : List Bool × List Bool → Bool)
    (extend : List Bool → Bool) (x u : List Bool) : List Bool :=
  if accept (x, u) then u
  else if extend (pairB x (u ++ [false])) then u ++ [false]
  else u ++ [true]

private theorem nextPrefix_length (accept : List Bool × List Bool → Bool)
    (extend : List Bool → Bool) (x u : List Bool) :
    (nextPrefix accept extend x u).length ≤ u.length + 1 := by
  unfold nextPrefix
  split
  · omega
  · split <;> simp

private theorem nextPrefix_extends
    {R : Set (List Bool × List Bool)}
    {accept : List Bool × List Bool → Bool} {extend : List Bool → Bool}
    (ha : ∀ x u, (x, u) ∈ R ↔ accept (x, u) = true)
    (he : ∀ x u, extend (pairB x u) = true ↔ ∃ w : List Bool, (x, u ++ w) ∈ R)
    {x u : List Bool} (h : ∃ w : List Bool, (x, u ++ w) ∈ R) :
    ∃ w : List Bool, (x, nextPrefix accept extend x u ++ w) ∈ R := by
  unfold nextPrefix
  split
  · exact h
  · rename_i hn
    split
    · rename_i hf
      exact (he x (u ++ [false])).mp hf
    · rename_i hf
      obtain ⟨w, hw⟩ := h
      cases w with
      | nil =>
          exact False.elim (hn ((ha x u).mp (by simpa using hw)))
      | cons b w =>
          cases b
          · exact False.elim (hf ((he x (u ++ [false])).mpr
              ⟨w, by simpa [List.append_assoc] using hw⟩))
          · exact ⟨w, by simpa [List.append_assoc] using hw⟩

private theorem cpt_prefixStep
    {accept : List Bool × List Bool → Bool} {extend : List Bool → Bool}
    (ha : ComputableInPolyTime encodePair Computability.encodeBool accept)
    (he : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool extend) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => pairB (unpairB s).1 (nextPrefix accept extend (unpairB s).1 (unpairB s).2)) := by
  have hfalse := cpt_app2 cpt_unpairB2 (cpt_const [false])
  have htrue := cpt_app2 cpt_unpairB2 (cpt_const [true])
  have htest := cpt_bitFlag (cpt_comp (cpt_pairB2 cpt_unpairB1 hfalse) he)
  have hsel := cpt_sel htest htrue hfalse
  have hstay := cpt_bitFlag (cpt_comp cpt_unpairB ha)
  refine cptE (cpt_pairB2 cpt_unpairB1 (cpt_sel hstay hsel cpt_unpairB2)) (fun s => ?_)
  simp only [sel, nextPrefix]
  cases accept (unpairB s) <;> cases extend (pairB (unpairB s).1 ((unpairB s).2 ++ [false])) <;> rfl

/-- A deterministic decider for extension queries yields a measured polynomial-time witness search. -/
theorem VerifierSearchFromPrefixDecider
    (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R)
    (bound : ∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length)
    (D : Language Bool) (hD : D ∈ P)
    (spec : ∀ x u : List Bool, List.replicate x.length true ++ false :: (x ++ u) ∈ D ↔
      ∃ w : List Bool, (x, u ++ w) ∈ R) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ x : List Bool, (∃ w : List Bool, (x, w) ∈ R) → (x, search x) ∈ R := by
  obtain ⟨accept, ha, hca⟩ := hR
  obtain ⟨extend, he, hce⟩ := hD
  have hspec (x u : List Bool) : extend (pairB x u) = true ↔ ∃ w : List Bool, (x, u ++ w) ∈ R :=
    (he (pairB x u)).symm.trans (spec x u)
  let step := fun s => pairB (unpairB s).1 (nextPrefix accept extend (unpairB s).1 (unpairB s).2)
  have hlen (s : List Bool) : (step s).length ≤ s.length + 2 := by
    have h := unpairB_length s
    have hn := nextPrefix_length accept extend (unpairB s).1 (unpairB s).2
    change (pairB _ _).length ≤ _
    rw [pairB_length]
    omega
  let search := fun x : List Bool => (unpairB (step^[p.eval x.length] (pairB x []))).2
  have hclock : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => List.replicate (p.eval x.length) true) := L055 p
  have hloop := cpt_iterGrow (cpt_prefixStep hca hce) 2 hlen hclock
    (cpt_pairB2 cpt_id (cpt_const []))
  have hsearch : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search :=
    cptE (cpt_unpairB2_1 hloop) (fun x => by simp [search, step])
  refine ⟨search, hsearch, fun x hx => ?_⟩
  have invariant (k : ℕ) : ∃ u : List Bool,
      step^[k] (pairB x []) = pairB x u ∧
      ((x, u) ∈ R ∨ u.length = k) ∧
      ∃ w : List Bool, (x, u ++ w) ∈ R := by
    induction k with
    | zero =>
        exact ⟨[], rfl, Or.inr rfl, by simpa using hx⟩
    | succ k ih =>
        obtain ⟨u, hstep, hsize, hw⟩ := ih
        refine ⟨nextPrefix accept extend x u, ?_, ?_,
          nextPrefix_extends (fun x u => ha (x, u)) hspec hw⟩
        · rw [Function.iterate_succ_apply', hstep]
          simp only [step, unpairB_pairB]
        · unfold nextPrefix
          split
          · rename_i h
            exact Or.inl ((ha (x, u)).mpr h)
          · rename_i h
            have hk := hsize.resolve_left (fun hu => h ((ha (x, u)).mp hu))
            right
            split <;> simp [hk]
  obtain ⟨u, hu, hsize, w, hw⟩ := invariant (p.eval x.length)
  have hs : search x = u := by simp [search, hu, unpairB_pairB]
  rw [hs]
  rcases hsize with ha | hk
  · exact ha
  · have hb := bound x (u ++ w) hw
    simp only [List.length_append, hk] at hb
    have hz : w.length = 0 := by omega
    have hn : w = [] := List.length_eq_zero_iff.mp hz
    simpa [hn] using hw

end PEqualNP.Outside
