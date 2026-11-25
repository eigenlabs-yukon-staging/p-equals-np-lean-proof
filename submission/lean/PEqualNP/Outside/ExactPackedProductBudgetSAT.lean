import PEqualNP.Outside.PackedProductBudgetSAT
import PEqualNP.Outside.MeasuredCappedClauseProduct
import PEqualNP.Library.L016
import PEqualNP.Library.L046
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

private def query (base extra : CNF) : List Bool := pairB (encodeCNF base) (encodeCNF extra)

private theorem canonical_in_p : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x} ∈ P := by
  have hm := cpt_comp (g := fun l : List Bool => !l.isEmpty)
    PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF bf_cpt_neL
  have he : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
    funext s
    cases wfB s <;> rfl
  rw [he] at hm
  exact ⟨wfB,fun s => (wfB_iff s).symm,hm⟩

private theorem pair_in_p : {x : List Bool | pairB (unpairB x).1 (unpairB x).2 = x} ∈ P := by
  have hflag := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF
    (cpt_pairB2 cpt_unpairB1 cpt_unpairB2) cpt_id
  have h := cpt_comp (g := fun l : List Bool => !l.isEmpty) hflag bf_cpt_neL
  have he : (fun x : List Bool =>
      !(bflag (decide (pairB (unpairB x).1 (unpairB x).2 = x))).isEmpty) =
      (fun x => decide (pairB (unpairB x).1 (unpairB x).2 = x)) := by
    funext x
    cases decide (pairB (unpairB x).1 (unpairB x).2 = x) <;> rfl
  rw [he] at h
  exact ⟨_,fun x => decide_eq_true_iff.symm,h⟩

/-- Exact packed branch language with an independently recognizable tractable base. -/
theorem ExactPackedProductBudgetSAT (G B : Language Bool) (hG : G ∈ P) (hB : B ∈ P)
    (hbase : ∀ base : CNF, encodeCNF base ∈ G → ∀ units : CNF, IsKCNF 1 units →
      (encodeCNF (base ++ units) ∈ B ↔ Satisfiable (base ++ units)))
    (q : Polynomial ℕ) :
    {x : List Bool | ∃ (base extra : CNF),
      List.replicate (encodeCNF base).length true ++ false :: (encodeCNF base ++ encodeCNF extra) = x ∧
      encodeCNF base ∈ G ∧ (extra.map List.length).prod ≤ q.eval x.length ∧
      Satisfiable (base ++ extra)} ∈ P := by
  obtain ⟨D,hD,hdec⟩ := PackedProductBudgetSAT B hB q
  obtain ⟨product,hp,hs⟩ := MeasuredCappedClauseProduct
  let canonical : Language Bool := {s | ∃ φ : CNF, encodeCNF φ = s}
  let baseSyntax : Language Bool := {x | (unpairB x).1 ∈ canonical ⊓ G}
  let extraSyntax : Language Bool := {x | (unpairB x).2 ∈ canonical}
  let pairSyntax : Language Bool := {x | pairB (unpairB x).1 (unpairB x).2 = x}
  let budget := fun x : List Bool => List.replicate (q.eval x.length) true
  let prod := fun x => product (true :: budget x,(unpairB x).2)
  let guard : Language Bool := {x | (prod x).length ≤ (budget x).length}
  have hBS : baseSyntax ∈ P := L016 baseSyntax (canonical ⊓ G)
    ⟨fun x => (unpairB x).1,cpt_unpairB1,fun _ => Iff.rfl⟩ (L046 canonical G canonical_in_p hG)
  have hES : extraSyntax ∈ P := L016 extraSyntax canonical
    ⟨fun x => (unpairB x).2,cpt_unpairB2,fun _ => Iff.rfl⟩ canonical_in_p
  have hprod : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) prod :=
    cpt_comp (cpt_pair (cpt_cons1 true (L055 q)) cpt_unpairB2) hp
  have hguard : guard ∈ P :=
    ⟨_,fun x => decide_eq_true_iff.symm,cpt_comp (cpt_pair (L055 q) hprod) LenCmp.lenLE_polyTime⟩
  have hsem (b e : CNF) : query b e ∈ guard ↔
      (e.map List.length).prod ≤ q.eval (query b e).length := by
    change (prod (query b e)).length ≤ (budget (query b e)).length ↔ _
    simp only [prod,query,unpairB_pairB,hs,budget,List.length_cons,List.length_replicate]
    omega
  let W := baseSyntax ⊓ extraSyntax ⊓ pairSyntax
  have hW : W ∈ P := L046 _ _ (L046 _ _ hBS hES) pair_in_p
  have h := L046 (W ⊓ guard) D (L046 W guard hW hguard) hD
  have he : {x : List Bool | ∃ (base extra : CNF), query base extra = x ∧
      encodeCNF base ∈ G ∧ (extra.map List.length).prod ≤ q.eval x.length ∧
      Satisfiable (base ++ extra)} = W ⊓ guard ⊓ D := by
    ext x
    change (∃ (base extra : CNF), query base extra = x ∧ encodeCNF base ∈ G ∧
      (extra.map List.length).prod ≤ q.eval x.length ∧ Satisfiable (base ++ extra)) ↔
      (((((∃ b : CNF, encodeCNF b = (unpairB x).1) ∧ (unpairB x).1 ∈ G) ∧
        (∃ e : CNF, encodeCNF e = (unpairB x).2)) ∧
        pairB (unpairB x).1 (unpairB x).2 = x) ∧ x ∈ guard) ∧ x ∈ D
    constructor
    · rintro ⟨b,e,rfl,gb,hb,hsat⟩
      have hbase' := hdec b e (hbase b gb) hb
      refine ⟨⟨?_,(hsem b e).mpr hb⟩,hbase'.mpr hsat⟩
      simp only [query,unpairB_pairB]
      exact ⟨⟨⟨⟨b,rfl⟩,gb⟩,⟨e,rfl⟩⟩,True.intro⟩
    · rintro ⟨⟨⟨⟨⟨⟨b,hb⟩,gb⟩,⟨e,he⟩⟩,hpair⟩,hg⟩,hd⟩
      have hquery : query b e = x := by rw [query,hb,he,hpair]
      have hgb : encodeCNF b ∈ G := hb.symm ▸ gb
      have hbound : (e.map List.length).prod ≤ q.eval x.length := by
        rw [← hquery]
        exact (hsem b e).mp (hquery.symm ▸ hg)
      have hd' : query b e ∈ D := hquery.symm ▸ hd
      have hbudget' : (e.map List.length).prod ≤ q.eval (query b e).length :=
        (hsem b e).mp (hquery.symm ▸ hg)
      exact ⟨b,e,hquery,hgb,hbound,(hdec b e (hbase b hgb) hbudget').mp hd'⟩
  change {x : List Bool | ∃ (base extra : CNF), query base extra = x ∧
    encodeCNF base ∈ G ∧ (extra.map List.length).prod ≤ q.eval x.length ∧ Satisfiable (base ++ extra)} ∈ P
  rwa [he]

end PEqualNP.Outside
