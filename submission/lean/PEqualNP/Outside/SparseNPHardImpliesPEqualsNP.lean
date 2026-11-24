import PEqualNP.Outside.SparseORLayeredSearch
import PEqualNP.Outside.NPWitnessPrefixBranch
import PEqualNP.Outside.PairedDisjunctionInNP
import PEqualNP.Library.L010

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.PrefixDecideHelpers (Word good extensions extensions_np cpt_test)
open PEqualNP.Outside.NPWitnessPrefixBranch
  (done children children_cpt children_growth extension_branch leaf)
open PEqualNP.Outside.PairedDisjunctionInNP (orLanguage in_np)
open PEqualNP.Outside.RecordPairScan (wire)

/-- Mahaney's theorem in the pinned machine model, using sparse OR-image pruning. -/
theorem PEqualNP.Outside.SparseNPHardImpliesPEqualsNP :
    ∀ (A : Language Bool) (r : Polynomial ℕ),
      (∀ n : ℕ, ∃ S : Finset (List Bool), S.card ≤ r.eval n ∧
        ∀ y, y ∈ S ↔ y ∈ A ∧ y.length ≤ n) →
      (∀ L : Language Bool, L ∈ NP → PolyTimeReducible L A) →
      P = NP := by
  intro A r hSparse hHard
  refine Set.Subset.antisymm PEqualNP.Library.L010 ?_
  intro L hL
  obtain ⟨R,p,hR,hLeq⟩ := hL
  let G := extensions R p
  have hG : G ∈ NP := extensions_np R p hR
  obtain ⟨f,hf,hred⟩ := hHard (orLanguage G) (in_np G hG)
  let F (q : Word × Word) : Word := f (pairB q.1 q.2)
  have hF : ComputableInPolyTime encodePair (fun w => w) F := cpt_comp cpt_pairB hf
  have hFn : ∀ x y : Word, F (x,y) ∈ A ↔ x ∈ G ∨ y ∈ G := by
    intro x y
    have hh := (hred (pairB x y)).symm
    change F (x,y) ∈ A ↔ (unpairB (pairB x y)).1 ∈ G ∨ (unpairB (pairB x y)).2 ∈ G at hh
    simpa only [unpairB_pairB] using hh
  obtain ⟨verify,hv,hc⟩ := hR
  let test := done verify p
  have hTest : ComputableInPolyTime (fun w : Word => w) Computability.encodeBool test :=
    cpt_test verify p hc
  have hGP : G ∈ P :=
    SparseORLayeredSearch G A r hSparse ⟨F,hF,hFn⟩ (children test) p 2
      (extension_branch R p verify hv) (children_growth test)
      ⟨wire,rfl,fun _ _ => rfl,children_cpt test hTest⟩ ⟨test,hTest,leaf R p verify hv⟩
  obtain ⟨dec,hd,hD⟩ := hGP
  let input (x : Word) := pairB x []
  have hi : ComputableInPolyTime (fun w : Word => w) (fun w : Word => w) input := by
    exact cpt_pairB2 cpt_id (cpt_const [])
  refine ⟨fun x => dec (input x), ?_, cpt_comp hi hD⟩
  intro x
  rw [← hd]
  exact (hLeq x).trans (by
    change (∃ w : Word, good R p x w) ↔
      ∃ t : Word, good R p (unpairB (pairB x [])).1 ((unpairB (pairB x [])).2 ++ t)
    simp only [unpairB_pairB, List.nil_append])
