import PEqualNP.Outside.PrefixClauseNames
import PEqualNP.Outside.UniqueNameScan
import PEqualNP.Outside.ExtractedBackdoor

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.PrefixNameCollector (collect collect_cpt)
open PEqualNP.Outside.PrefixClauseNames (prefixNames collect_enc)
open PEqualNP.Outside.UniqueNameScan (scan unique unique_cpt unique_enc scan_count mem_scan)

private theorem prefix_width (φ : CNF) :
    ∀ c ∈ φ, (c.filter (fun l => decide (l.1 ∉ scan [] (prefixNames φ)))).length ≤ 2 := by
  intro c hc
  let keep := fun l : Literal => decide (l.1 ∉ scan [] (prefixNames φ))
  let n := c.length - 2
  have hnil : (c.take n).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro l hl
    have hmem : l.1 ∈ prefixNames φ :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
    have hm := (mem_scan l.1 [] (prefixNames φ)).mpr (Or.inr hmem)
    simp [keep, hm]
  have e : c.filter keep = (c.drop n).filter keep := by
    calc
      _ = (c.take n ++ c.drop n).filter keep :=
        congrArg (List.filter keep) (List.take_append_drop n c).symm
      _ = _ := by rw [List.filter_append, hnil, List.nil_append]
  change (c.filter keep).length ≤ 2
  rw [e]
  apply (List.length_filter_le _ _).trans
  simp only [List.length_drop, n]
  omega

theorem PEqualNP.Outside.PrefixClauseSATInP (p : Polynomial ℕ) :
    ∃ L : Language Bool, L ∈ P ∧ (∀ x, x ∈ L → x ∈ SAT) ∧
      ∀ φ : CNF,
        2 ^ (φ.flatMap (fun c => (c.take (c.length - 2)).map Prod.fst)).toFinset.card ≤
          p.eval (encodeCNF φ).length →
        (encodeCNF φ ∈ L ↔ Satisfiable φ) := by
  obtain ⟨L, hp, hs, hc⟩ := ExtractedBackdoor.solve p
    (fun φ => scan [] (prefixNames φ)) (fun x => unique (collect x))
    (cpt_comp collect_cpt unique_cpt)
    (fun φ => by simp only [collect_enc, unique_enc]) prefix_width
  refine ⟨L, hp, hs, fun φ hb => hc φ ?_⟩
  rw [scan_count]
  exact hb
