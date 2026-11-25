import PEqualNP.Outside.ComponentwiseRUPSearch
import PEqualNP.Outside.MeasuredTwoSATRUPSearch
import PEqualNP.Outside.MeasuredRenamableHornRUPSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

/-- Combine the width-two and renamable-Horn RUP generators across
independent components, with exact verification of each returned certificate. -/
theorem HybridComponentRUPSearch :
    let part := fun (φ : CNF) (x : ℕ) => φ.filter (fun c =>
      @decide (∃ m ∈ c, Relation.ReflTransGen (fun a b : ℕ =>
        ∃ d ∈ φ, a ∈ d.map Prod.fst ∧ b ∈ d.map Prod.fst) x m.1) (Classical.propDecidable _))
    let valid := fun (φ : CNF) (w : List Bool) =>
      w.length ≤ 2*(encodeCNF φ).length+6 ∧ ∃ ρ : CNF, encodeCNF ρ = w ∧
        IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
          (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (search (encodeCNF φ) ≠ [] → valid φ (search (encodeCNF φ))) ∧
        ((∀ c ∈ φ, ∀ l ∈ c,
          let p := part φ l.1
          IsKCNF 2 p ∨ ∃ r : Assignment, ∀ d ∈ p,
            ((d.map (fun m => (m.1,xor m.2 (r m.1)))).filter (fun m => m.2)).length ≤ 1) →
          (search (encodeCNF φ) = [] ↔ Satisfiable φ) ∧
            (¬Satisfiable φ → valid φ (search (encodeCNF φ)))) := by
  classical
  obtain ⟨first,hfirst,h1s⟩ := MeasuredRenamableHornRUPSearch
  obtain ⟨second,hsecond,h2s⟩ := MeasuredTwoSATRUPSearch
  obtain ⟨check,hcheck,hcs⟩ := measured_bounded_refutation
  let gen := fun x => sel (if check (x,first x) then [true] else []) (second x) (first x)
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen :=
    cpt_sel (cpt_bitFlag (cpt_comp (cpt_pair cpt_id hfirst) hcheck)) hsecond hfirst
  have good_first (φ : CNF)
      (h : ∃ r : Assignment, ∀ c ∈ φ, ((c.map (fun m => (m.1,xor m.2 (r m.1)))).filter fun m => m.2).length ≤ 1)
      (hs : ¬ Satisfiable φ) : boundedRefutation φ (first (encodeCNF φ)) := by
    obtain ⟨he,hr⟩ := (h1s φ h).2 hs
    rw [he]
    have hlen : (encodeCNF ([[]] : CNF)).length = 2 := rfl
    exact ⟨by omega,[[]],rfl,hr,by simp⟩
  have good_second (φ : CNF) (h : IsKCNF 2 φ)
      (hs : ¬ Satisfiable φ) : boundedRefutation φ (second (encodeCNF φ)) := by
    obtain ⟨ρ,he,_,hlen,hr,h0⟩ := (h2s φ h).2 hs
    exact ⟨he.symm ▸ hlen,ρ,he.symm,hr,h0⟩
  obtain ⟨search,hsearch,hss⟩ := ComponentwiseRUPSearch gen hg
  refine ⟨search,hsearch,fun φ => ?_⟩
  have hsound : search (encodeCNF φ) ≠ [] → boundedRefutation φ (search (encodeCNF φ)) := (hss φ).1
  refine ⟨hsound,fun hshape => ?_⟩
  have hc (l : Literal) (c : Clause) (hmem : l :: c ∈ φ) (hns : ¬ Satisfiable (component φ l.1)) :
      boundedRefutation (component φ l.1) (gen (encodeCNF (component φ l.1))) := by
    let p := component φ l.1
    change boundedRefutation p (gen (encodeCNF p))
    by_cases h : check (encodeCNF p,first (encodeCNF p)) = true
    · simpa [gen,sel,h] using (hcs p _).mp h
    · have h' := hshape (l :: c) hmem l List.mem_cons_self
      rcases h' with hb | hh
      · simpa [gen,sel,h] using good_second p hb hns
      · exact (h ((hcs p _).mpr (good_first p hh hns))).elim
  have hiff : search (encodeCNF φ) = [] ↔ Satisfiable φ := (hss φ).2 hc
  exact ⟨hiff,fun hn => hsound (fun h => hn (hiff.mp h))⟩

end PEqualNP.Outside
