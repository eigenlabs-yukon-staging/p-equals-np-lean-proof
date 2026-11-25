import PEqualNP.Outside.MeasuredResolutionSaturation
import PEqualNP.Outside.ExactResolutionRefutationVerifier
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Search

/-- Fixed-width resolution search returns a checked refutation exactly when
one exists at the given width. The empty result does not assert satisfiability. -/
theorem MeasuredBoundedWidthRefutationSearch (k : ℕ) :
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF,
        (search (encodeCNF φ) ≠ [] ↔ ∃ π : List (PEqualNP.ProofComplexity.Clause ℕ),
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} π ∧
          ∀ d ∈ π, Finset.card d ≤ k) ∧
        (search (encodeCNF φ) ≠ [] → ∃ ρ : CNF, search (encodeCNF φ) = encodeCNF ρ ∧
          PEqualNP.ProofComplexity.IsRefutation
            {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d} (ρ.map List.toFinset) ∧
          ∀ d ∈ ρ.map List.toFinset, Finset.card d ≤ k) := by
  obtain ⟨derive,hd,hds⟩ := MeasuredResolutionSaturation k
  let R : Set (List Bool × List Bool) := {p | ∃ φ ρ : CNF, encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
    PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset)}
  have hR : DecidableInPolyTime encodePair R := ExactResolutionRefutationVerifier.1
  obtain ⟨verify,hvs,hv⟩ := hR
  let test := fun x => verify (x,derive x)
  let search := fun x => sel (if test x then [true] else []) [] (derive x)
  have hs : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search :=
    cpt_sel (cpt_bitFlag (cpt_comp (cpt_pair cpt_id hd) hv)) (cpt_const []) hd
  refine ⟨search,hs,fun φ => ?_⟩
  obtain ⟨ρ,hρ,hD,hw,he⟩ := hds φ
  have hdR : test (encodeCNF φ) = true ↔
      PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset) := by
    change verify (encodeCNF φ,derive (encodeCNF φ)) = true ↔ _
    rw [hρ,← hvs]
    constructor
    · rintro ⟨f,p,hf,hp,hr⟩
      have h1 := encodeCNF_injective hf
      have h2 := encodeCNF_injective hp
      subst f p
      exact hr
    · exact fun h => ⟨φ,ρ,rfl,rfl,h⟩
  have goal : search (encodeCNF φ) ≠ [] ↔
      PEqualNP.ProofComplexity.IsRefutation (clauseSet φ) (ρ.map List.toFinset) := by
    rw [← hdR]
    constructor
    · intro h
      cases hh : test (encodeCNF φ) with
      | false =>
          have bad : search (encodeCNF φ) = [] := by simp [search,sel,hh]
          exact (h bad).elim
      | true => rfl
    · intro h
      have hr := hdR.mp h
      have hne : encodeCNF ρ ≠ [] := by
        intro h0
        have hρ0 := encodeCNF_injective (h0.trans (show [] = encodeCNF [] by rfl))
        subst ρ
        exact List.not_mem_nil hr.2
      simp [search,sel,h,hρ,hne]
  constructor
  · rw [goal]
    constructor
    · exact fun h => ⟨_,h,hw⟩
    · intro h
      have h' := he.mpr h
      exact ⟨hD,List.mem_map.mpr ⟨[],h',List.toFinset_nil⟩⟩
  · intro h
    have hr := goal.mp h
    have hh := hdR.mpr hr
    exact ⟨ρ,by simp [search,sel,hh,hρ],hr,hw⟩

end PEqualNP.Outside
