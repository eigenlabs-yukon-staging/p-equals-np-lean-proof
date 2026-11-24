import PEqualNP.Outside.PrefixDecideHelpers
import PEqualNP.Outside.SatCodePrimitives
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.Padding

namespace PEqualNP.Outside.TwoWitnesses

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.PrefixDecideHelpers (Word Rel good)
open PEqualNP.Library.SearchHelpers.TwoSat (cpt_eqF)

def first (q : Word × Word) : Word := (unpairB q.2).1
def second (q : Word × Word) : Word := (unpairB q.2).2

theorem first_cpt : ComputableInPolyTime encodePair (fun w : Word => w) first := by
  unfold first
  exact cpt_comp (f := Prod.snd) (g := fun w : Word => (unpairB w).1) cpt_snd cpt_unpairB1

theorem second_cpt : ComputableInPolyTime encodePair (fun w : Word => w) second := by
  unfold second
  exact cpt_comp (f := Prod.snd) (g := fun w : Word => (unpairB w).2) cpt_snd cpt_unpairB2

def differs (q : Word × Word) : Bool := (bflag (decide (first q = second q))).isEmpty

theorem differs_cpt : ComputableInPolyTime encodePair Computability.encodeBool differs := by
  have h1 := cpt_comp cpt_unpairB first_cpt
  have h2 := cpt_comp cpt_unpairB second_cpt
  have h := cpt_comp (cpt_eqF h1 h2) cpt_isEmpty
  exact cptl (cpt_comp cpt_pairB h) (fun q => by simp [differs, unpairB_pairB, bflag])

theorem differs_iff (q : Word × Word) : differs q = true ↔ first q ≠ second q := by
  by_cases h : first q = second q <;> simp [differs, bflag, h]

theorem and_cpt {f g : Word × Word → Bool}
    (hf : ComputableInPolyTime encodePair Computability.encodeBool f)
    (hg : ComputableInPolyTime encodePair Computability.encodeBool g) :
    ComputableInPolyTime encodePair Computability.encodeBool (fun q => f q && g q) :=
  cptl (nf_restrict (nf_and (cpt_comp nfDec_polyTime hf) (cpt_comp nfDec_polyTime hg)))
    (fun q => by simp [nfDec_encodePair, Bool.and_comm])

def rel (R : Rel) (p : Polynomial ℕ) : Rel :=
  {q | good R p q.1 (first q) ∧ good R p q.1 (second q) ∧ first q ≠ second q}

theorem rel_cpt (R : Rel) (p : Polynomial ℕ) (hR : DecidableInPolyTime encodePair R) :
    DecidableInPolyTime encodePair (rel R p) := by
  obtain ⟨dec, hs,hc⟩ := hR
  let f (q : Word × Word) := decide ((first q).length ≤ p.eval q.1.length) && dec (q.1,first q)
  let g (q : Word × Word) := decide ((second q).length ≤ p.eval q.1.length) && dec (q.1,second q)
  have hnf := nf_decider dec p hc
  have hf : ComputableInPolyTime encodePair Computability.encodeBool f :=
    cptl (cpt_comp (cpt_pairG (f := Prod.fst) (g := first) cpt_fst first_cpt) hnf) (fun _ => rfl)
  have hg : ComputableInPolyTime encodePair Computability.encodeBool g :=
    cptl (cpt_comp (cpt_pairG (f := Prod.fst) (g := second) cpt_fst second_cpt) hnf) (fun _ => rfl)
  refine ⟨fun q => f q && (g q && differs q), ?_, and_cpt hf (and_cpt hg differs_cpt)⟩
  intro q
  change good R p q.1 (first q) ∧ good R p q.1 (second q) ∧ first q ≠ second q ↔ _
  simp only [good, Bool.and_eq_true, f, g, decide_eq_true_eq, differs_iff, hs]

def language (R : Rel) (p : Polynomial ℕ) : Language Bool :=
  {x | ∃ u v : Word, good R p x u ∧ good R p x v ∧ u ≠ v}

theorem np (R : Rel) (p : Polynomial ℕ) (hR : DecidableInPolyTime encodePair R) :
    language R p ∈ NP := by
  refine ⟨rel R p, Polynomial.C 3 * p + Polynomial.C 1, rel_cpt R p hR, ?_⟩
  intro x
  constructor
  · rintro ⟨u,v,hu,hv,hd⟩
    refine ⟨pairB u v, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, pairB_length]
      have h1 := hu.1
      have h2 := hv.1
      omega
    · simpa [rel, first, second, unpairB_pairB] using And.intro hu (And.intro hv hd)
  · rintro ⟨w, _, hw⟩
    exact ⟨first (x,w), second (x,w), hw⟩

end PEqualNP.Outside.TwoWitnesses

open PEqualNP.Library

theorem PEqualNP.Outside.AtLeastTwoWitnessesInNP :
    ∀ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), DecidableInPolyTime encodePair R →
      ∃ L : Language Bool, L ∈ NP ∧
        ∀ x, x ∈ L ↔ ∃ u v : List Bool,
          (u.length ≤ p.eval x.length ∧ (x,u) ∈ R) ∧
          (v.length ≤ p.eval x.length ∧ (x,v) ∈ R) ∧ u ≠ v := by
  intro R p hR
  exact ⟨TwoWitnesses.language R p, TwoWitnesses.np R p hR, fun _ => Iff.rfl⟩
