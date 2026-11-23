import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Machines.NormalForm
import PEqualNP.Outside.PrefixIteration

namespace PEqualNP.Outside.PrefixDecideHelpers

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

abbrev Word := List Bool
abbrev Rel := Set (Word × Word)
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def good (R : Rel) (p : Polynomial ℕ) (x w : Word) : Prop :=
  w.length ≤ p.eval x.length ∧ (x, w) ∈ R

def extensions (R : Rel) (p : Polynomial ℕ) : Language Bool :=
  {z | ∃ t : Word, good R p (unpairB z).1 ((unpairB z).2 ++ t)}

theorem cpt_joinPrefix :
    ComputableInPolyTime encodePair encodePair
      (fun q : Word × Word => ((unpairB q.1).1, (unpairB q.1).2 ++ q.2)) := by
  apply cpt_pairG
  · have h := cpt_comp cpt_fst cpt_unpairB1
    exact h
  · exact cpt_comp (cpt_first cpt_unpairB2) cpt_append

theorem cpt_test (verify : Word × Word → Bool) (p : Polynomial ℕ)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool verify) :
    ComputableInPolyTime (fun x : Word => x) Computability.encodeBool
      (fun z => decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)) :=
  cpt_comp cpt_unpairB (nf_decider verify p hc)

theorem eval_mono_nat (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

theorem extensions_np (R : Rel) (p : Polynomial ℕ) (hR : DecidableInPolyTime encodePair R) :
    extensions R p ∈ NP := by
  obtain ⟨verify, hv, hc⟩ := hR
  refine ⟨{q | good R p (unpairB q.1).1 ((unpairB q.1).2 ++ q.2)}, p, ?_, ?_⟩
  · refine ⟨fun q => decide (((unpairB q.1).2 ++ q.2).length ≤ p.eval (unpairB q.1).1.length)
         && verify ((unpairB q.1).1, (unpairB q.1).2 ++ q.2), ?_, ?_⟩
    · intro q
      simp only [Set.mem_ofPred_eq, good, Bool.and_eq_true, decide_eq_true_eq, hv]
    · exact cpt_comp cpt_joinPrefix (nf_decider verify p hc)
  · intro z
    change (∃ t, good R p (unpairB z).1 ((unpairB z).2 ++ t)) ↔
      ∃ t, t.length ≤ p.eval z.length ∧ good R p (unpairB z).1 ((unpairB z).2 ++ t)
    constructor
    · rintro ⟨t, ht⟩
      have hb := ht.1
      simp only [List.length_append] at hb
      have hx : (unpairB z).1.length ≤ z.length := by
        have hh := unpairB_length z
        omega
      exact ⟨t, (Nat.le_trans (by omega : t.length ≤ p.eval (unpairB z).1.length)
        (eval_mono_nat p hx)), ht⟩
    · rintro ⟨t, _, ht⟩
      exact ⟨t, ht⟩

end PEqualNP.Outside.PrefixDecideHelpers
