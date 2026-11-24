import PEqualNP.Outside.PrefixDecideHelpers

namespace PEqualNP.Outside.PrefixSelector

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.PrefixDecideHelpers
open PEqualNP.Outside.PrefixIteration (advance iterate_correct)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (done canExtend : Word → Bool) (z : Word) : Word :=
  let x := (unpairB z).1
  let pre := (unpairB z).2
  pairB x (advance (fun w => done (pairB x w)) (fun w => canExtend (pairB x w)) pre)

theorem step_cpt {done canExtend : Word → Bool}
    (hd : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool done)
    (he : ComputableInPolyTime (fun x : Word => x) Computability.encodeBool canExtend) :
    CPT (step done canExtend) := by
  have snoc (b : Bool) : CPT (fun z => (unpairB z).2 ++ [b]) :=
    cpt_app2 cpt_unpairB2 (cpt_const [b])
  have packed (b : Bool) : CPT (fun z => pairB (unpairB z).1 ((unpairB z).2 ++ [b])) :=
    cpt_pairB2 cpt_unpairB1 (snoc b)
  have reset := cpt_pairB2 cpt_unpairB1 cpt_unpairB2
  have hflagD := cpt_bitFlag (cpt_comp reset hd)
  have hflagE := cpt_bitFlag (cpt_comp (packed false) he)
  have transfer {f : Word → Word} (hf : CPT f) (eq : ∀ z, f z = step done canExtend z) :
      CPT (step done canExtend) := (funext eq) ▸ hf
  refine transfer (cpt_sel hflagD (cpt_sel hflagE (packed true) (packed false)) reset) ?_
  intro z
  cases hd' : done (pairB (unpairB z).1 (unpairB z).2) <;>
    cases he' : canExtend (pairB (unpairB z).1 ((unpairB z).2 ++ [false])) <;>
    simp [step, advance, sel, hd', he']

theorem step_grows (done canExtend : Word → Bool) (z : Word) :
    (step done canExtend z).length ≤ z.length + 2 := by
  simp only [step, pairB_length]
  have h := unpairB_length z
  have hg := PrefixIteration.advance_length
    (fun w => done (pairB (unpairB z).1 w))
    (fun w => canExtend (pairB (unpairB z).1 w)) (unpairB z).2
  omega

theorem iterate_packed (done canExtend : Word → Bool) (x pre : Word) (n : ℕ) :
    (step done canExtend)^[n] (pairB x pre) =
      pairB x ((advance (fun w => done (pairB x w))
        (fun w => canExtend (pairB x w)))^[n] pre) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [step, unpairB_pairB]

theorem selector_of_extensions (R : Rel) (p : Polynomial ℕ)
    (hR : DecidableInPolyTime encodePair R) (he : extensions R p ∈ P) :
    ∃ s : Word → Word, CPT s ∧
      ∀ x : Word, (∃ w : Word, good R p x w) → good R p x (s x) := by
  obtain ⟨verify, hv, hc⟩ := hR
  obtain ⟨canExtend, he_spec, he_cpt⟩ := he
  let done : Word → Bool := fun z =>
    decide ((unpairB z).2.length ≤ p.eval (unpairB z).1.length) && verify (unpairB z)
  let g := step done canExtend
  have hcpt : CPT g := step_cpt (cpt_test verify p hc) he_cpt
  let s := fun x : Word => (unpairB (g^[p.eval x.length] (pairB x []))).2
  refine ⟨s, ?_, ?_⟩
  · exact clocked_selector hcpt p (step_grows done canExtend)
  · intro x hx
    have hd' : ∀ w : Word, done (pairB x w) = true ↔ good R p x w := by
      intro w
      simp only [done, unpairB_pairB, good, Bool.and_eq_true, decide_eq_true_eq, hv]
    have he' : ∀ w : Word, canExtend (pairB x w) = true ↔ ∃ t, good R p x (w ++ t) := by
      intro w
      rw [← he_spec]
      change (∃ t, good R p (unpairB (pairB x w)).1 ((unpairB (pairB x w)).2 ++ t)) ↔ _
      simp only [unpairB_pairB]
    change good R p x (unpairB ((step done canExtend)^[p.eval x.length] (pairB x []))).2
    rw [iterate_packed, unpairB_pairB]
    exact iterate_correct _ _ _ hd' he' (p.eval x.length) (fun _ h => h.1) _ []
      (by simp) (by simpa using hx)

end PEqualNP.Outside.PrefixSelector
