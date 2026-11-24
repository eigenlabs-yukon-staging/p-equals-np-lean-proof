import PEqualNP.Outside.HornRenamingCompiler
import PEqualNP.Library.L030
import PEqualNP.Library.SearchHelpers.Encoding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.HornRenamingFacts
open PEqualNP.Outside.HornRenamingCompiler (compile compile_cpt compile_enc)

private theorem wfFlag_cpt :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (wfB x)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private theorem pair_mem (φ : CNF) :
    encodeCNF (pairCNF φ) ∈ KSAT 2 ↔
      ∃ ρ : Assignment, ∀ c ∈ φ, (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1 := by
  have hc : encodeCNF (pairCNF φ) ∈ KSAT 2 ↔ Satisfiable (pairCNF φ) := by
    constructor
    · rintro ⟨ψ, _, he, hs⟩
      rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
    · exact fun h => ⟨pairCNF φ, pairCNF_two φ, rfl, h⟩
  rw [hc]
  refine exists_congr (fun ρ => (pairCNF_correct ρ φ).trans ?_)
  constructor
  · intro h c he
    have hh := h (renameClause ρ c) (List.mem_map.mpr ⟨c, he, rfl⟩)
    simpa [renameClause, List.filter_map, Function.comp_def] using hh
  · intro h c he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    simpa [renameClause, List.filter_map, Function.comp_def] using h d hd

private theorem no_mem : encodeCNF ([[]] : CNF) ∉ KSAT 2 := by
  rintro ⟨φ, _, he, σ, hs⟩
  rw [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
  simp [CNF.eval, Clause.eval] at hs

theorem PEqualNP.Outside.RenamableHornReducesToTwoSAT :
    ∃ L : Language Bool,
      (∀ x, x ∈ L ↔ ∃ φ : CNF, encodeCNF φ = x ∧
        ∃ ρ : Assignment, ∀ c ∈ φ, (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1) ∧
      PolyTimeReducible L (KSAT 2) ∧ L ∈ P := by
  let L : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    ∃ ρ : Assignment, ∀ c ∈ φ, (c.filter fun l => xor l.2 (ρ l.1)).length ≤ 1}
  let red (x : List Bool) := sel (bflag (wfB x)) (encodeCNF ([[]] : CNF)) (compile x)
  have ht : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) red :=
    cpt_sel wfFlag_cpt (cpt_const (encodeCNF ([[]] : CNF))) compile_cpt
  have hs (x : List Bool) : x ∈ L ↔ red x ∈ KSAT 2 := by
    cases hx : wfB x
    · have hn : ¬ ∃ φ : CNF, encodeCNF φ = x := by
        intro h
        have hh := (wfB_iff x).mpr h
        simp [hx] at hh
      change (∃ φ : CNF, encodeCNF φ = x ∧ _) ↔ _
      constructor
      · rintro ⟨φ, h, _⟩
        exact False.elim (hn ⟨φ, h⟩)
      · have he : red x = encodeCNF ([[]] : CNF) := by simp [red, hx, bflag, sel]
        rw [he]
        exact fun h => False.elim (no_mem h)
    · obtain ⟨φ, rfl⟩ := (wfB_iff x).mp hx
      have he : red (encodeCNF φ) = encodeCNF (pairCNF φ) := by
        simp [red, hx, bflag, sel, compile_enc]
      rw [he, pair_mem]
      constructor
      · rintro ⟨ψ, h, ρ, hr⟩
        obtain rfl := PEqualNP.Library.SearchHelpers.encodeCNF_injective h
        exact ⟨ρ, hr⟩
      · exact fun h => ⟨φ, rfl, h⟩
  obtain ⟨dec, hd, hc⟩ := L030
  exact ⟨L, fun _ => Iff.rfl, ⟨red, ht, hs⟩,
    ⟨fun x => dec (red x), fun x => (hs x).trans (hd _), cpt_comp ht hc⟩⟩
