import PEqualNP.Outside.PositiveGraphCorrespondence
import PEqualNP.Outside.PositiveBudgetVerifier
import PEqualNP.Library.L031

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Outside.PositiveGraphCompile (graph compile compile_cpt compile_enc)
open PEqualNP.Outside.PositiveGraphCorrespondence (mem_compiled compiled_iff expected)
open PEqualNP.Outside.PositiveGraphSourceCorrect (vcode_len)
open PEqualNP.Outside.PositiveBudgetVerifier (language language_np language_enc shape)
open PEqualNP.Outside.MonotoneTwoCNFWeightReduction (weight)

private abbrev Word := List Bool

private theorem wfFlag_cpt : ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)
    (fun w => bflag (wfB w)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

private def noInstance : Word := pairB (encodeCNF [[(0, true)]]) []

private theorem noInstance_not : noInstance ∉ language := by
  rw [noInstance, language_enc]
  rintro ⟨_, σ, hsat, hweight⟩
  have hv : σ 0 = true := by simpa [CNF.eval, Clause.eval, Literal.eval] using hsat
  simp [weight, hv] at hweight

private theorem compiled_entry (φ : CNF) : compile (encodeCNF φ) ∈ language ↔ Satisfiable φ := by
  rw [compile_enc, language_enc, vcode_len]
  have hs : shape (graph φ) := by
    intro c hc
    rcases (mem_compiled φ c).mp hc with rfl | ⟨r, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, _, rfl⟩ <;> simp
  rw [and_iff_right hs, ← compiled_iff φ]
  apply exists_congr
  intro σ
  apply and_congr_right
  intro _
  omega

private def reduceSAT (w : Word) : Word := sel (bflag (wfB w)) noInstance (compile w)

private theorem reduceSAT_cpt :
    ComputableInPolyTime (fun w : Word => w) (fun w : Word => w) reduceSAT :=
  cpt_sel wfFlag_cpt (cpt_const noInstance) compile_cpt

private theorem reduceSAT_correct (x : Word) : x ∈ SAT ↔ reduceSAT x ∈ language := by
  cases hw : wfB x
  · have h : x ∉ SAT := by
      rintro ⟨φ, he, _⟩
      have hgood := (wfB_iff _).mpr ⟨φ, he⟩
      rw [hw] at hgood
      contradiction
    simp [reduceSAT, hw, h, noInstance_not, bflag, sel]
  · obtain ⟨φ, rfl⟩ := (wfB_iff _).mp hw
    have h : encodeCNF φ ∈ SAT ↔ Satisfiable φ := by
      constructor
      · rintro ⟨ψ, he, hs⟩
        rwa [PEqualNP.Library.SearchHelpers.encodeCNF_injective he] at hs
      · exact fun hs => ⟨φ, rfl, hs⟩
    simpa [reduceSAT, hw, bflag, sel] using h.trans (compiled_entry φ).symm

theorem PEqualNP.Outside.PositiveTwoCNFWeightBudgetNPComplete :
    ∃ L : Language Bool, L ∈ NP ∧ (∀ A ∈ NP, PolyTimeReducible A L) ∧
      ∀ (φ : CNF) (b : List Bool),
        let x := encodeCNF φ
        (List.replicate x.length true ++ false :: (x ++ b)) ∈ L ↔
          (∀ c ∈ φ, (c.length = 1 ∨ c.length = 2) ∧ c.all Prod.snd = true) ∧
          ∃ σ : Assignment, CNF.eval σ φ = true ∧
            2 * ((φ.flatMap fun c => c.map Prod.fst).toFinset.filter
              (fun i => σ i = true)).card ≤ b.length := by
  refine ⟨language, language_np, ?_, language_enc⟩
  intro A hA
  obtain ⟨reduction, hc, hs⟩ := L031.2 A hA
  exact ⟨fun w => reduceSAT (reduction w), cpt_comp hc reduceSAT_cpt, fun w =>
    (hs w).trans (reduceSAT_correct (reduction w))⟩
