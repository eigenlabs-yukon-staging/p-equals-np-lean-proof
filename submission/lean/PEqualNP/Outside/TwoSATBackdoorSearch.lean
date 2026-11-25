import PEqualNP.Outside.ExactTwoSATBackdoor
import PEqualNP.Outside.SparseVariableSATSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

private theorem backdoor_units (k : ℕ) (φ : CNF) (ls : List Literal)
    (h : ∃ xs : List ℕ, xs.length ≤ k ∧
      IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) :
    ∃ xs : List ℕ, xs.length ≤ k ∧
      IsKCNF 2 ((φ ++ ls.map (fun l => [l])).map
        (fun c => c.filter (fun l => decide (l.1 ∉ xs)))) := by
  obtain ⟨xs,hx,hw⟩ := h
  refine ⟨xs,hx,fun c hc => ?_⟩
  rw [List.map_append,List.mem_append] at hc
  rcases hc with hc | hc
  · exact hw c hc
  · rw [List.map_map,List.mem_map] at hc
    obtain ⟨l,_,rfl⟩ := hc
    have h := List.length_filter_le (fun l : Literal => decide (l.1 ∉ xs)) [l]
    change (List.filter (fun a : Literal => decide (a.1 ∉ xs)) [l]).length ≤ 2
    exact h.trans (by simp)

/-- Sparse satisfying assignments are computable in the reference model for
every satisfiable CNF with a 2-CNF deletion backdoor of fixed size. -/
theorem TwoSATBackdoorSearch (k : ℕ) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∃ xs : List ℕ, xs.length ≤ k ∧
        IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let D : Language Bool := {x | ∃ φ : CNF, encodeCNF φ = x ∧
    (∃ xs : List ℕ, xs.length ≤ k ∧ IsKCNF 2 (φ.map (fun c => c.filter (fun l => decide (l.1 ∉ xs))))) ∧
    Satisfiable φ}
  obtain ⟨search,hsearch,hs⟩ := SparseVariableSATSearch D (ExactTwoSATBackdoor k).2
  refine ⟨search,hsearch,fun φ h => hs φ (fun ls => ?_)⟩
  let ψ : CNF := φ ++ ls.map (fun l => [l])
  change encodeCNF ψ ∈ D ↔ Satisfiable ψ
  constructor
  · rintro ⟨f,henc,_,hsat⟩
    exact encodeCNF_injective henc ▸ hsat
  · intro hsat
    exact ⟨ψ,rfl,backdoor_units k φ ls h,hsat⟩

end PEqualNP.Outside
