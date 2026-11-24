import PEqualNP.Outside.BoundedNPWitnessIsolation

open PEqualNP.Library
open PEqualNP.Outside.NPWitnessIsolation (Word words goodWords mem_goodWords)

private theorem words_card (n : ℕ) : (words n).card + 1 = 2 ^ (n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    classical
    let f := (words n).image (false :: ·)
    let t := (words n).image (true :: ·)
    have hdis : Disjoint f t := by
      refine Finset.disjoint_left.mpr ?_
      intro z hz hz'
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v, _, he⟩ := Finset.mem_image.mp hz'
      simp at he
    have hnil : ([] : Word) ∉ f ∪ t := by
      intro he
      rcases Finset.mem_union.mp he with he | he <;> obtain ⟨w, _, h⟩ := Finset.mem_image.mp he <;> simp at h
    have hf : f.card = (words n).card :=
      Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
    have ht : t.card = (words n).card :=
      Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
    change (insert [] (f ∪ t)).card + 1 = _
    rw [Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdis, hf, ht, pow_succ]
    omega

theorem PEqualNP.Outside.PinnedNPWitnessFinset :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
        (W : List Bool → Finset (List Bool)),
        DecidableInPolyTime encodePair R ∧
        (∀ x w, w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R) ∧
        (∀ x, x ∈ L ↔ (W x).Nonempty) ∧
        ∀ x, (W x).card + 1 ≤ 2 ^ (p.eval x.length + 1) := by
  intro L hL
  obtain ⟨R,p,hR,hs⟩ := hL
  refine ⟨R,p,goodWords R p,hR,mem_goodWords R p, ?_, ?_⟩
  · intro x
    exact (hs x).trans (exists_congr (fun w => (mem_goodWords R p x w).symm))
  · intro x
    rw [← words_card]
    classical
    unfold goodWords
    exact Nat.add_le_add_right (Finset.card_filter_le _ _) _
