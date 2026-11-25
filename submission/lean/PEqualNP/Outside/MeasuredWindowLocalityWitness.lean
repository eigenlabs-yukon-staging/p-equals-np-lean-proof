import PEqualNP.Outside.MeasuredLocalityClauseUniverse
import PEqualNP.Outside.LocalityUniverseCoverage
import PEqualNP.Outside.MeasuredEliminationWitness
import PEqualNP.Outside.MeasuredVariableOrderCode

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private abbrev Raw := List Bool

/-- Generate a bounded window catalogue from the input and use it to
recover a sparse satisfying assignment for first-occurrence-local CNFs. -/
theorem MeasuredWindowLocalityWitness (k : ℕ) :
    let varCode := fun i : ℕ => (i.bits.flatMap fun b => [true,b]) ++ [false,true]
    ∃ catalogue search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) catalogue ∧
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      (∀ φ : CNF, ∃ U : CNF, catalogue (encodeCNF φ) = encodeCNF U ∧
        U.length ≤ 1 + φ.flatten.length * 2^(2*(k+1))) ∧
      ∀ φ : CNF,
        let order := φ.flatten.map Prod.fst
        (∀ c ∈ φ, ∀ l ∈ c, ∀ m ∈ c, order.idxOf l.1 ≤ order.idxOf m.1 + k) →
        let result := search (encodeCNF φ)
        (result = [] ↔ ¬ Satisfiable φ) ∧
        (Satisfiable φ → ∃ vs : List ℕ, result = true :: vs.flatMap varCode ∧
          CNF.eval (fun x => decide (x ∈ vs)) φ = true) := by
  dsimp only
  obtain ⟨gen,hg,hgs⟩ := MeasuredLocalityClauseUniverse k
  obtain ⟨norm,hn,hns⟩ := MeasuredVariableOrderCode
  obtain ⟨recover,hr,hrs⟩ := MeasuredEliminationWitness
  let catalogue := fun s : Raw => gen (norm s)
  let search := fun s : Raw => recover (pairB (norm s) (pairB s (catalogue s)))
  have hc : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) catalogue := cpt_comp hn hg
  have hs : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) search :=
    cpt_comp (cpt_pairB2 hn (cpt_pairB2 cpt_id hc)) hr
  refine ⟨catalogue,search,hc,hs,?_,fun φ hLoc => ?_⟩
  · intro φ
    obtain ⟨U,hU,hSize,_⟩ := hgs (φ.flatten.map (fun l => (l.1,true)))
    refine ⟨U,?_,?_⟩
    · simpa only [catalogue,hns] using hU
    · simpa only [List.length_map] using hSize
  · let order := φ.flatten.map Prod.fst
    let c := φ.flatten.map (fun l => (l.1,true))
    have hNorm : norm (encodeCNF φ) = encodeClause c := hns φ
    have hOrder : c.map Prod.fst = order := by simp [c,order,List.map_map,Function.comp_def]
    have hCode : c = order.map (fun x => (x,true)) := by simp [c,order,List.map_map,Function.comp_def]
    obtain ⟨U,hU,_,hRep⟩ := hgs c
    have hLoc' : ∀ d ∈ clauseSet φ, ∀ l ∈ d, ∀ m ∈ d, order.idxOf l.1 ≤ order.idxOf m.1 + k := by
      rintro d ⟨e,he,rfl⟩ l hl m hm
      exact hLoc e he l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm)
    have hSupp : ∀ d ∈ clauseSet φ, ∀ l ∈ d, l.1 ∈ order := by
      rintro d ⟨e,he,rfl⟩ l hl
      exact List.mem_map.mpr ⟨l,List.mem_flatten.mpr ⟨e,he,List.mem_toFinset.mp hl⟩,rfl⟩
    have hCov := LocalityUniverseCoverage k (clauseSet φ) c U hRep
    rw [hOrder] at hCov
    have hCover := hCov hLoc' hSupp
    let spec := fun r : Raw => (r = [] ↔ ¬ Satisfiable φ) ∧
      (Satisfiable φ → ∃ vs : List ℕ, r = true :: vs.flatMap
        (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
        CNF.eval (fun x => decide (x ∈ vs)) φ = true)
    have heq : search (encodeCNF φ) =
        recover (pairB (encodeClause (order.map (fun x => (x,true))))
          (pairB (encodeCNF φ) (encodeCNF U))) := by
      simp only [search,catalogue,hNorm,hU]
      rw [hCode]
    change spec (search (encodeCNF φ))
    rw [heq]
    exact hrs φ U order hSupp hCover

end PEqualNP.Outside
