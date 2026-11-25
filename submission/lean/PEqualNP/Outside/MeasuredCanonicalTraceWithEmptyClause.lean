import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

private def markEmpty (p : List Bool × List Bool) : List Bool := sel (hd p.2) [true] []

private theorem mark_cpt : ComputableInPolyTime encodePair (fun x : List Bool => x) markEmpty := by
  have h := cpt_sel (cpt_hd1 cpt_unpairB2) (cpt_const [true]) (cpt_const [])
  change ComputableInPolyTime _ _ (fun p : List Bool × List Bool => sel (hd p.2) [true] [])
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

private theorem mark_spec (arg : List Bool) (c : Clause) : markEmpty (arg,encodeClause c) ≠ [] ↔ c = [] := by
  cases c with
  | nil => simp [markEmpty,encodeClause,sel,hd]
  | cons l c =>
      have he : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      rw [he,encodeLiteral_eq]
      simp [markEmpty,hd,sel]

private theorem measured_empty :
    ∃ flag : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) flag ∧
      ∀ φ : CNF, flag (encodeCNF φ) ≠ [] ↔ [] ∈ φ := by
  obtain ⟨scan,hs,hspec⟩ := MeasuredClauseMap markEmpty mark_cpt
  refine ⟨fun x => scan ([],x),cpt_comp (cpt_pair (cpt_const []) cpt_id) hs,fun φ => ?_⟩
  simp only [hspec,ne_eq,List.flatMap_eq_nil_iff]
  classical
  push Not
  constructor
  · rintro ⟨c,hc,h⟩
    exact (mark_spec [] c).mp h ▸ hc
  · exact fun he => ⟨[],he,(mark_spec [] []).mpr rfl⟩

/-- Combine a measured canonical trace predicate with exact raw syntax
and the requirement that at least one recorded clause is empty. -/
theorem MeasuredCanonicalTraceWithEmptyClause (valid : CNF → CNF → Prop)
    (learn : List Bool × List Bool → Bool)
    (hlearn : ComputableInPolyTime encodePair Computability.encodeBool learn)
    (hls : ∀ φ ρ : CNF, learn (encodeCNF φ,encodeCNF ρ) = true ↔ valid φ ρ) :
    DecidableInPolyTime encodePair
      {p : List Bool × List Bool | ∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
        valid φ ρ ∧ [] ∈ ρ} := by
  obtain ⟨empty,hempty,hes⟩ := measured_empty
  let good := fun p : List Bool × List Bool => wfB p.1 && wfB p.2 && learn p && !(empty p.2).isEmpty
  have hlearn' := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hlearn)
  have h1 := cpt_comp cpt_unpairB1 cpt_wfF
  have h2 := cpt_comp cpt_unpairB2 cpt_wfF
  have h3 := cpt_comp cpt_unpairB2 hempty
  have hb := cpt_sel h1 (cpt_const []) (cpt_sel h2 (cpt_const []) (cpt_sel hlearn' (cpt_const []) h3))
  have ht := cpt_comp (g := fun v : List Bool => !v.isEmpty) (cpt_comp cpt_pairB hb) bf_cpt_neL
  have he :
      (fun p : List Bool × List Bool => !(sel (bflag (wfB p.1)) []
        (sel (bflag (wfB p.2)) [] (sel (if learn p then [true] else []) [] (empty p.2)))).isEmpty) = good := by
    funext p
    unfold good
    cases wfB p.1 <;> cases wfB p.2 <;> cases learn p <;> rfl
  simp only [unpairB_pairB] at ht
  rw [he] at ht
  refine ⟨good,fun p => ?_,ht⟩
  change
    (∃ (φ ρ : CNF), encodeCNF φ = p.1 ∧ encodeCNF ρ = p.2 ∧
      valid φ ρ ∧ [] ∈ ρ) ↔ good p = true
  simp only [good,Bool.and_eq_true,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  rcases p with ⟨x,w⟩
  constructor
  · rintro ⟨φ,ρ,rfl,rfl,hr,he⟩
    exact ⟨⟨⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(wfB_iff _).mpr ⟨ρ,rfl⟩⟩,(hls φ ρ).mpr hr⟩,(hes ρ).mpr he⟩
  · rintro ⟨⟨⟨hx,hw⟩,hl⟩,he⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff _).mp hx
    obtain ⟨ρ,rfl⟩ := (wfB_iff _).mp hw
    exact ⟨φ,ρ,rfl,rfl,(hls φ ρ).mp hl,(hes ρ).mp he⟩

end PEqualNP.Outside
