import PEqualNP.Outside.P_subset_NP
import PEqualNP.Library.L008
import PEqualNP.Library.Universal.PrimsCPT

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside (P_subset_NP)

private abbrev Word := List Bool

private def existsWord (H : Language Bool) (p : Polynomial ℕ) : Language Bool :=
  {x | ∃ w : Word, w.length ≤ p.eval x.length ∧ pairB x w ∈ H}

private theorem exists_np (H : Language Bool) (p : Polynomial ℕ) (hH : H ∈ P) :
    existsWord H p ∈ NP := by
  obtain ⟨dec, hd, hc⟩ := hH
  exact ⟨{q : Word × Word | pairB q.1 q.2 ∈ H}, p,
    ⟨fun q => dec (pairB q.1 q.2), fun q => hd _, cpt_comp cpt_pairB hc⟩, fun _ => Iff.rfl⟩

private def quant (stage : Bool × Polynomial ℕ) (next : Word → Prop) (x : Word) : Prop :=
  if stage.1 then ∀ w : Word, w.length ≤ stage.2.eval x.length → next (pairB x w)
  else ∃ w : Word, w.length ≤ stage.2.eval x.length ∧ next (pairB x w)

private theorem decides (he : P = NP) (H : Language Bool) (hH : H ∈ P)
    (stages : List (Bool × Polynomial ℕ)) :
    ∃ L : Language Bool, L ∈ P ∧ ∀ x, x ∈ L ↔ stages.foldr quant (fun y => y ∈ H) x := by
  induction stages with
  | nil => exact ⟨H, hH, fun _ => Iff.rfl⟩
  | cons q qs ih =>
    obtain ⟨M, hM, hs⟩ := ih
    cases hq : q.1
    · have hN := exists_np M q.2 hM
      rw [← he] at hN
      refine ⟨existsWord M q.2, hN, ?_⟩
      intro x
      change (∃ w : Word, w.length ≤ q.2.eval x.length ∧ pairB x w ∈ M) ↔
        quant q (qs.foldr quant (fun y => y ∈ H)) x
      rw [quant, hq]
      simp only [Bool.false_eq_true, ite_false]
      exact exists_congr (fun w => and_congr_right (fun _ => hs _))
    · have hN := exists_np Mᶜ q.2 (L008 M hM)
      rw [← he] at hN
      refine ⟨(existsWord Mᶜ q.2)ᶜ, L008 _ hN, ?_⟩
      intro x
      change (¬ ∃ w : Word, w.length ≤ q.2.eval x.length ∧ pairB x w ∉ M) ↔
        quant q (qs.foldr quant (fun y => y ∈ H)) x
      rw [quant, hq]
      simp only [ite_true]
      constructor
      · intro h w hw
        apply (hs _).mp
        by_contra hh
        exact h ⟨w, hw, hh⟩
      · intro h
        rintro ⟨w, hw, hnot⟩
        exact hnot ((hs _).mpr (h w hw))

theorem PEqualNP.Outside.FiniteQuantifiedWordCollapse :
    P = NP ↔
      ∀ (H : Language Bool), H ∈ P → ∀ (stages : List (Bool × Polynomial ℕ)),
        ∃ L : Language Bool, L ∈ P ∧ ∀ x : List Bool,
          x ∈ L ↔ stages.foldr (fun q next y =>
            let extend (w : List Bool) := List.replicate y.length true ++ false :: (y ++ w)
            if q.1 then ∀ w : List Bool, w.length ≤ q.2.eval y.length → next (extend w)
            else ∃ w : List Bool, w.length ≤ q.2.eval y.length ∧ next (extend w))
            (fun y => y ∈ H) x := by
  constructor
  · exact decides
  · intro all
    apply Set.Subset.antisymm P_subset_NP
    intro L hL
    obtain ⟨R, p, ⟨dec, hd, hc⟩, hs⟩ := hL
    let H : Language Bool := {z | unpairB z ∈ R}
    have hH : H ∈ P := ⟨fun x => dec (unpairB x), fun x => hd _, cpt_comp cpt_unpairB hc⟩
    obtain ⟨M, hM, hspec⟩ := all H hH [(false, p)]
    have he : L = M := by
      ext x
      have hm : x ∈ M ↔ ∃ w : Word, w.length ≤ p.eval x.length ∧ pairB x w ∈ H := hspec x
      change x ∈ L ↔ x ∈ M
      refine (hs x).trans ?_
      refine Iff.trans ?_ hm.symm
      refine exists_congr (fun w => and_congr_right (fun _ => ?_))
      change (x, w) ∈ R ↔ unpairB (pairB x w) ∈ R
      rw [unpairB_pairB]
    exact he.symm ▸ hM
