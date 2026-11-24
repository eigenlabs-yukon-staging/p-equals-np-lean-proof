import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.AlternatingNameScan

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def rest (z : Word) : Word := (unpairB z).1
def flag (z : Word) : Word := (unpairB (unpairB z).2).1
def out (z : Word) : Word := (unpairB (unpairB z).2).2
def pack (r f o : Word) : Word := pairB r (pairB f o)

def step (z : Word) : Word :=
  let r := rest z
  let f := flag z
  let o := out z
  sel r z (pack (dropI r) (sel f [true] []) (sel f o (o ++ headI r)))

theorem step_cpt : CPT step := by
  have hr : CPT rest := cpt_unpairB1
  have hf : CPT flag := cpt_unpairB1_1 cpt_unpairB2
  have ho : CPT out := cpt_unpairB2_1 cpt_unpairB2
  have hnew := cpt_sel hf ho (cpt_app2 ho (cpt_comp hr cpt_headI))
  have hflip := cpt_sel hf (cpt_const [true]) (cpt_const [])
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 (cpt_comp hr cpt_dropI) (cpt_pairB2 hflip hnew)))
    (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 4 := by
  have h₁ := unpairB_length z
  have h₂ := unpairB_length (unpairB z).2
  have h₃ := congrArg List.length (headI_dropI (rest z))
  simp only [rest, List.length_append] at h₃
  simp only [step, sel]
  split
  · omega
  · split
    · simp only [pack, pairB_length, List.length_cons, List.length_nil, rest, out]
      omega
    · simp only [pack, pairB_length, List.length_nil, List.length_append, rest, out]
      omega

theorem step_conserves (z : Word) :
    (rest (step z)).length + (out (step z)).length ≤ (rest z).length + (out z).length := by
  have h := congrArg List.length (headI_dropI (rest z))
  simp only [List.length_append] at h
  simp only [step, sel]
  split
  · omega
  · simp only [pack, rest, out, unpairB_pairB] at h ⊢
    split
    · omega
    · simp only [List.length_append]
      omega

def sieve (q : Word × Word) : Word :=
  out (step^[q.1.length] (pack q.1 q.2 []))

theorem sieve_cpt : ComputableInPolyTime encodePair (fun x : Word => x) sieve := by
  obtain ⟨c⟩ := step_cpt
  have loop := Iter.iter_polyTime step c 4 step_length
  have seed := cpt_comp cpt_pairB
    (cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const [])))
  have hseed : ComputableInPolyTime encodePair (fun x : Word => x)
      (fun q : Word × Word => pack q.1 q.2 []) :=
    cptl seed (fun q => by simp [pack, unpairB_pairB])
  have h := cpt_comp (cpt_comp (cpt_pairG hseed cpt_fst) loop)
    (cpt_unpairB2_1 cpt_unpairB2)
  exact h

theorem run_conserves (n : ℕ) (z : Word) :
    (rest (step^[n] z)).length + (out (step^[n] z)).length ≤ (rest z).length + (out z).length := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (step_conserves z)

theorem sieve_length (q : Word × Word) : (sieve q).length ≤ q.1.length := by
  have h := run_conserves q.1.length (pack q.1 q.2 [])
  simp only [rest, out, pack, unpairB_pairB, List.length_nil, Nat.add_zero] at h
  exact (Nat.le_add_left _ _).trans h

def alternating {α : Type} (keep : Bool) : List α → List α
  | [] => []
  | x :: xs => (if keep then [x] else []) ++ alternating (!keep) xs

theorem step_item (v : ℕ) (r o : Word) (keep : Bool) :
    step (pack (vcode v ++ r) (bflag keep) o) =
      pack r (bflag (!keep)) (o ++ if keep then vcode v else []) := by
  cases keep <;> simp [step, pack, rest, flag, out, sel, bflag, unpairB_pairB,
    headI_vcode, dropI_vcode, vcode_ne_nil]

theorem run_codes (vs acc : List ℕ) (keep : Bool) :
    ∃ f : Bool,
      step^[vs.length] (pack (vs.flatMap vcode) (bflag keep) (acc.flatMap vcode)) =
        pack [] (bflag f) ((acc ++ alternating keep vs).flatMap vcode) := by
  induction vs generalizing acc keep with
  | nil => exact ⟨keep, by simp [alternating]⟩
  | cons i vs ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons, step_item]
    cases keep
    · simpa [alternating] using ih acc true
    · simpa [alternating, List.flatMap_append, List.append_assoc] using ih (acc ++ [i]) false

theorem sieve_codes (vs : List ℕ) (keep : Bool) :
    sieve (vs.flatMap vcode, bflag keep) = (alternating keep vs).flatMap vcode := by
  obtain ⟨f, h⟩ := run_codes vs [] keep
  have hlen := length_le_flatMap_vcode vs
  have hfix : step (pack [] (bflag f) ((alternating keep vs).flatMap vcode)) =
      pack [] (bflag f) ((alternating keep vs).flatMap vcode) := by
    simp [step, rest, pack, unpairB_pairB, sel]
  simp only [List.flatMap_nil, List.nil_append] at h
  simp only [sieve, Prod.fst, Prod.snd]
  rw [← Nat.sub_add_cancel hlen, Function.iterate_add_apply, h, Function.iterate_fixed hfix]
  simp [out, pack, unpairB_pairB]

end PEqualNP.Outside.AlternatingNameScan
