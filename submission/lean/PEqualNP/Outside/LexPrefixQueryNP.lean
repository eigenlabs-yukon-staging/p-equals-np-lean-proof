import PEqualNP.Outside.LexicographicWordCompare
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "Verifier" => Word × Word → Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "ltBit" => (fun a b : Bool => !a && b)

def lexPrefixQuery (v : Verifier) : Language Bool :=
  {s | ∃ w : Word, v ((unpairB s).1, w) = true ∧
    (unpairB s).2.lex (w.take (unpairB s).2.length) ltBit = false}

theorem lexPrefixQuery_pair (v : Verifier) (x pre : Word) :
    pairB x pre ∈ lexPrefixQuery v ↔
      ∃ w : Word, v (x,w) = true ∧ pre.lex (w.take pre.length) ltBit = false := by
  change (∃ w : Word, v ((unpairB (pairB x pre)).1, w) = true ∧
    (unpairB (pairB x pre)).2.lex (w.take (unpairB (pairB x pre)).2.length) ltBit =
      false) ↔ _
  rw [unpairB_pairB]

private def leftVerify (v : Verifier) (p : Word × Word) : Bool :=
  let query := unpairB p.1
  let pre := query.2
  !pre.lex (p.2.take pre.length) ltBit && v (query.1, p.2)

private theorem leftVerify_cpt {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v) :
    ComputableInPolyTime encodePair Computability.encodeBool (leftVerify v) := by
  have hquery := cpt_unpairB1
  have hw := cpt_unpairB2
  have hpre := cpt_unpairB2_1 hquery
  have hx := cpt_unpairB1_1 hquery
  have htake := PEqualNP.Library.SearchHelpers.Tab.StepW.cpt_tk hpre hw
  have hcmp := cpt_bitFlag (cpt_comp (cpt_pair hpre htake) LexicographicWordCompare)
  have htest := cpt_bitFlag (cpt_comp (cpt_pair hx hw) hv)
  have hf := cpt_comp cpt_pairB (cpt_comp (cpt_sel hcmp htest (cpt_const [])) bf_cpt_neL)
  apply bf_cptl hf
  rintro ⟨z,w⟩
  simp only [unpairB_pairB, PEqualNP.Library.SearchHelpers.Tab.StepW.tk_eq, leftVerify]
  cases h₁ : ((unpairB z).2.lex (w.take (unpairB z).2.length) ltBit) <;>
    cases h₂ : v ((unpairB z).1,w) <;> simp [h₁,h₂,bflag]

theorem lexPrefixQuery_np {v : Verifier}
    (hv : ComputableInPolyTime encodePair Computability.encodeBool v)
    (p : Polynomial Nat) (bound : ∀ x w : Word, v (x,w) = true → w.length ≤ p.eval x.length) :
    lexPrefixQuery v ∈ NP := by
  refine ⟨{q | leftVerify v q = true}, p,
    ⟨leftVerify v, fun _ => Iff.rfl, leftVerify_cpt hv⟩, fun s => ?_⟩
  change (∃ w : Word, v ((unpairB s).1,w) = true ∧
      (unpairB s).2.lex (w.take (unpairB s).2.length) ltBit = false) ↔
    ∃ w : Word, w.length ≤ p.eval s.length ∧ leftVerify v (s,w) = true
  have hlen : (unpairB s).1.length ≤ s.length := by have h := unpairB_length s; omega
  constructor
  · rintro ⟨w, hw, hcmp⟩
    exact ⟨w, (bound _ _ hw).trans (eval_mono p hlen), by simp [leftVerify, hcmp, hw]⟩
  · rintro ⟨w, _, hw⟩
    have hc := Bool.and_eq_true_iff.mp hw
    exact ⟨w, hc.2, by simpa using hc.1⟩

/-- Testing whether a bounded witness exists whose prefix is at most a given word
in lexicographic order defines a pinned NP language. -/
theorem LexPrefixQueryNP (R : Set (Word × Word)) (hR : DecidableInPolyTime encodePair R)
    (p : Polynomial Nat) (bound : ∀ x w : Word, (x,w) ∈ R → w.length ≤ p.eval x.length) :
    ∃ A : Language Bool, A ∈ NP ∧
      ∀ x t : Word,
        (List.replicate x.length true ++ false :: (x ++ t)) ∈ A ↔
          ∃ w : Word, (x,w) ∈ R ∧ t.lex (w.take t.length) ltBit = false := by
  obtain ⟨v, spec, hv⟩ := hR
  have hb (x w : Word) (h : v (x,w) = true) := bound x w ((spec (x,w)).mpr h)
  refine ⟨lexPrefixQuery v, lexPrefixQuery_np hv p hb, fun x t => ?_⟩
  refine (lexPrefixQuery_pair v x t).trans ?_
  simp only [← spec]

end PEqualNP.Outside
