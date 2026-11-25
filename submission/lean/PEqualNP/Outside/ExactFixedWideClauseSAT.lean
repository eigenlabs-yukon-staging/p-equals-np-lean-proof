import PEqualNP.Library.L016
import PEqualNP.Library.L046
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Outside.CNFWideClausePacking
import PEqualNP.Outside.MeasuredCNFClauseCount
import PEqualNP.Outside.FixedWideClauseSAT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

/-- The exact reference-encoded SAT language with at most a fixed number of
clauses wider than two is in P, with no bound on the widths of those clauses. -/
theorem ExactFixedWideClauseSAT (k : ℕ) :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (φ.filter (fun c => 2 < c.length)).length ≤ k ∧ Satisfiable φ} ∈ P := by
  obtain ⟨pack, hpack, hshape⟩ := CNFWideClausePacking
  obtain ⟨count, hcount, hcountSpec⟩ := MeasuredCNFClauseCount
  obtain ⟨D, hD, hdec⟩ := FixedWideClauseSAT k
  let valid : Language Bool := {s | ∃ φ : CNF, encodeCNF φ = s}
  let within : Language Bool := {s | (count (unpairB (pack s)).2).length ≤ k}
  let accepted : Language Bool := {s | pack s ∈ D}
  have hvalid : valid ∈ P :=
    ⟨wfB, fun s => (wfB_iff s).symm, cpt_comp (g := fun l : List Bool => !l.isEmpty)
      PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF
      bf_cpt_neL |> fun hm => by
        have e : (fun s => !(bflag (wfB s)).isEmpty) = wfB := by
          funext s
          cases wfB s <;> rfl
        rwa [← e]⟩
  have hwithin : within ∈ P := by
    have hn := cpt_comp (cpt_unpairB2_1 hpack) hcount
    have hc := cpt_pair (cpt_const (List.replicate k true)) hn
    refine ⟨fun s => decide ((count (unpairB (pack s)).2).length ≤ k), fun s => ?_, ?_⟩
    · exact decide_eq_true_iff.symm
    · have hm := cpt_comp hc LenCmp.lenLE_polyTime
      simpa only [List.length_replicate] using hm
  have haccepted : accepted ∈ P := L016 accepted D ⟨pack,hpack,fun _ => Iff.rfl⟩ hD
  have h := L046 (valid ⊓ within) accepted (L046 valid within hvalid hwithin) haccepted
  have hspec (φ : CNF) :
      encodeCNF φ ∈ within ↔ (φ.filter (fun c => 2 < c.length)).length ≤ k := by
    change (count (unpairB (pack (encodeCNF φ))).2).length ≤ k ↔ _
    have hp : pack (encodeCNF φ) =
      pairB (encodeCNF ((φ.filter (fun c => c.length ≤ 2)).reverse))
        (encodeCNF ((φ.filter (fun c => 2 < c.length)).reverse)) := hshape φ
    rw [hp, unpairB_pairB, hcountSpec, List.length_replicate, List.length_reverse]
  have hcorrect (φ : CNF) (hn : (φ.filter (fun c => 2 < c.length)).length ≤ k) :
      encodeCNF φ ∈ accepted ↔ Satisfiable φ := by
    let base := (φ.filter (fun c => c.length ≤ 2)).reverse
    let extra := (φ.filter (fun c => 2 < c.length)).reverse
    have hb : IsKCNF 2 base := by
      intro c hc
      have hc' := (List.mem_filter.mp (List.mem_reverse.mp hc)).2
      simpa using hc'
    have he : extra.length ≤ k := by simp [extra, hn]
    have hdec' := hdec base extra hb he
    change pack (encodeCNF φ) ∈ D ↔ _
    rw [hshape, hdec']
    apply exists_congr
    intro σ
    simp only [CNF.eval, List.all_eq_true, List.mem_append, base, extra, List.mem_reverse]
    have hm (c : Clause) : c ∈ List.filter (fun c => c.length ≤ 2) φ ∨
        c ∈ List.filter (fun c => 2 < c.length) φ ↔ c ∈ φ := by
      by_cases hc : c.length ≤ 2
      · simp [hc, show ¬2 < c.length by omega]
      · simp [hc, show 2 < c.length by omega]
    simp only [hm]
  have hset : {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      (φ.filter (fun c => 2 < c.length)).length ≤ k ∧ Satisfiable φ} =
      valid ⊓ within ⊓ accepted := by
    ext x
    change (∃ φ : CNF, encodeCNF φ = x ∧
      (φ.filter (fun c => 2 < c.length)).length ≤ k ∧ Satisfiable φ) ↔
      ((∃ φ : CNF, encodeCNF φ = x) ∧ x ∈ within) ∧ x ∈ accepted
    constructor
    · rintro ⟨φ,rfl,hn,hs⟩
      exact ⟨⟨⟨φ,rfl⟩,(hspec φ).mpr hn⟩,(hcorrect φ hn).mpr hs⟩
    · rintro ⟨⟨⟨φ,rfl⟩,hn⟩,hs⟩
      have hn' := (hspec φ).mp hn
      exact ⟨φ,rfl,hn',(hcorrect φ hn').mp hs⟩
  rwa [hset]

end PEqualNP.Outside
