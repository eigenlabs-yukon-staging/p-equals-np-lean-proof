import PEqualNP.Outside.CnfRestrictionSemantics

namespace PEqualNP.Outside.CnfRestrictionChoices

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionSemantics
open PEqualNP.Outside.CnfRestrictionMachine (Word)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (z : Word) : Word :=
  let r := (unpairB z).1
  let code := (unpairB (unpairB z).2).1
  let out := (unpairB (unpairB z).2).2
  sel r z (pairB (dropI r)
    (pairB code.tail (out ++ sel (bflag (code.headD false)) [] (headI r))))

theorem step_cpt : CPT step := by
  have hR := cpt_unpairB1
  have hCode := cpt_unpairB1_1 cpt_unpairB2
  have hOut := cpt_unpairB2_1 cpt_unpairB2
  have hHead := cpt_comp hR cpt_headI
  exact cptl (cpt_sel hR cpt_id (cpt_pairB2 (cpt_comp hR cpt_dropI)
    (cpt_pairB2 (cpt_tail1 hCode)
      (cpt_app2 hOut (cpt_sel (cpt_comp hCode cpt_firstF) (cpt_const []) hHead))))) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 2 := by
  have h1 := unpairB_length z
  have h2 := unpairB_length (unpairB z).2
  have h3 := congrArg List.length (headI_dropI (unpairB z).1)
  simp only [List.length_append] at h3
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length, List.length_append, List.length_tail]
    split <;> (try simp only [List.length_nil]) <;> omega

def choose (p : Word × Word) : Word :=
  (unpairB (unpairB (step^[p.1.length] (pairB p.1 (pairB p.2 [])))).2).2

theorem choose_cpt : ComputableInPolyTime encodePair (fun x : Word => x) choose := by
  obtain ⟨c⟩ := step_cpt
  have hLoop := Iter.iter_polyTime step c 2 step_length
  have hseed := cpt_comp cpt_pairB (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have seed : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun p : Word × Word => pairB p.1 (pairB p.2 [])) :=
    cptl hseed (fun p => by simp [unpairB_pairB])
  have h := cpt_comp (cpt_comp (cpt_pairG seed cpt_fst) hLoop) (cpt_unpairB2_1 cpt_unpairB2)
  exact h

def chosen : List ℕ → Word → List ℕ
  | [], _ => []
  | i :: rest, code =>
    if code.headD false then i :: chosen rest code.tail else chosen rest code.tail

theorem chosen_map (vs : List ℕ) (σ : ℕ → Bool) :
    chosen vs (vs.map σ) = vs.filter σ := by
  induction vs with
  | nil => rfl
  | cons i vs ih =>
    cases h : σ i <;> simp [chosen, ih, h]

theorem step_names (i : ℕ) (r code out : Word) :
    step (pairB (vcode i ++ r) (pairB code out)) =
      pairB r (pairB code.tail (out ++ if code.headD false then vcode i else [])) := by
  cases h : code.head?.getD false <;>
    simp [step, sel, bflag, vcode_ne_nil, unpairB_pairB, dropI_vcode, headI_vcode, h]

theorem run_names (vs : List ℕ) (code : Word) (out : List ℕ) :
    ∃ left : Word,
      step^[vs.length] (pairB (names vs) (pairB code (names out))) =
        pairB [] (pairB left (names (out ++ chosen vs code))) := by
  induction vs generalizing code out with
  | nil => exact ⟨code, by simp [chosen, names]⟩
  | cons i vs ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, names, List.flatMap_cons, step_names]
    cases h : code.head?.getD false
    · simpa [chosen, names, h] using ih code.tail out
    · simpa [chosen, names, h, List.flatMap_append, List.append_assoc] using ih code.tail (out ++ [i])

theorem choose_names (vs : List ℕ) (code : Word) :
    choose (names vs, code) = names (chosen vs code) := by
  obtain ⟨left, hrun⟩ := run_names vs code []
  have hlen : vs.length ≤ (names vs).length := length_le_flatMap_vcode vs
  have hfix : step (pairB [] (pairB left (names (chosen vs code)))) =
      pairB [] (pairB left (names (chosen vs code))) := by simp [step, sel, unpairB_pairB]
  simp only [names, List.flatMap_nil, List.nil_append] at hrun
  simp only [choose, Prod.fst, Prod.snd, names]
  simp only [names] at hlen hfix
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, hrun, Function.iterate_fixed hfix]
  simp [unpairB_pairB]

end PEqualNP.Outside.CnfRestrictionChoices
