import PEqualNP.Outside.PrefixDecideHelpers
import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.PairedDisjunctionInNP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.PrefixDecideHelpers (Word Rel good eval_mono_nat)

def orLanguage (G : Language Bool) : Language Bool :=
  {z | (unpairB z).1 ∈ G ∨ (unpairB z).2 ∈ G}

def selected (z w : Word) : Word :=
  sel (bflag (w.headD false)) (unpairB z).1 (unpairB z).2

def selectedCPT (z : Word) : Word × Word :=
  (selected (unpairB z).1 (unpairB z).2, (unpairB z).2.tail)

theorem selected_cpt :
    ComputableInPolyTime (fun x : Word => x) encodePair selectedCPT := by
  have hz := cpt_unpairB1
  have hw := cpt_unpairB2
  have hb := cpt_comp hw cpt_firstF
  have hc := cpt_sel hb (cpt_unpairB1_1 hz) (cpt_unpairB2_1 hz)
  exact cptl (cpt_pair hc (cpt_tail1 hw)) (fun _ => rfl)

theorem selected_length (z w : Word) : (selected z w).length ≤ z.length := by
  have h := unpairB_length z
  unfold selected sel
  split <;> omega

theorem in_np (G : Language Bool) (hG : G ∈ NP) : orLanguage G ∈ NP := by
  obtain ⟨R,p,hR,hG⟩ := hG
  obtain ⟨dec,hd,hc⟩ := hR
  let R' : Rel := {q | good R p (selected q.1 q.2) q.2.tail}
  refine ⟨R',p+1,?_,?_⟩
  · let D (q : Word × Word) := decide (q.2.tail.length ≤ p.eval (selected q.1 q.2).length) &&
      dec (selected q.1 q.2,q.2.tail)
    have h := cpt_comp (cpt_comp cpt_pairB selected_cpt) (nf_decider dec p hc)
    exact ⟨D, (fun q => by simp [D, R', good, hd]), cptl h (fun q => by
      simp [selectedCPT, D, unpairB_pairB])⟩
  · intro z
    change ((unpairB z).1 ∈ G ∨ (unpairB z).2 ∈ G) ↔
      ∃ w : Word, w.length ≤ (p+1).eval z.length ∧ good R p (selected z w) w.tail
    have hgood (b : Bool) (u : Word)
        (hu : good R p (if b then (unpairB z).2 else (unpairB z).1) u) :
        ∃ w : Word, w.length ≤ (p+1).eval z.length ∧ good R p (selected z w) w.tail := by
      have he : selected z (b :: u) = (if b then (unpairB z).2 else (unpairB z).1) := by
        cases b <;> simp [selected, sel, bflag]
      have hl : p.eval (selected z (b :: u)).length ≤ p.eval z.length :=
        (eval_mono_nat p) (selected_length z (b :: u))
      refine ⟨b :: u,?_,?_⟩
      · rw [he] at hl
        have ht := hu.1.trans hl
        simp only [List.length_cons, Polynomial.eval_add, Polynomial.eval_one]
        omega
      · simpa only [he, List.tail_cons] using hu
    constructor
    · rintro (ha | hb)
      · obtain ⟨u,hu⟩ := (hG _).mp ha
        exact hgood false u hu
      · obtain ⟨u,hu⟩ := (hG _).mp hb
        exact hgood true u hu
    · rintro ⟨w,_,hw⟩
      have h := (hG _).mpr ⟨w.tail,hw⟩
      unfold selected sel at h
      split at h
      · exact Or.inl h
      · exact Or.inr h

end PEqualNP.Outside.PairedDisjunctionInNP

open PEqualNP.Library PEqualNP.Library.Universal
open PEqualNP.Outside.PairedDisjunctionInNP (orLanguage in_np)

theorem PEqualNP.Outside.PairedDisjunctionInNP :
    ∀ G : Language Bool, G ∈ NP →
      ∃ H : Language Bool, H ∈ NP ∧
        ∀ x y : List Bool,
          (List.replicate x.length true ++ false :: (x ++ y)) ∈ H ↔ x ∈ G ∨ y ∈ G := by
  intro G hG
  refine ⟨orLanguage G, in_np G hG, ?_⟩
  intro x y
  change (unpairB (pairB x y)).1 ∈ G ∨ (unpairB (pairB x y)).2 ∈ G ↔ _
  rw [unpairB_pairB]
