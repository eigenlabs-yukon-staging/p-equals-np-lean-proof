import PEqualNP.Library.SearchHelpers.SatVerifierCPT

/-!
These transducer and membership helper proofs are adapted from the Apache-2.0
reference `PEqualNP.Library.SearchHelpers.SatVerifierCPT` module. The reference
marks them private, so this module exposes the needed facts for the decoder.
-/

namespace PEqualNP.Outside.SatCodePrimitives

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
open PEqualNP.Library.SearchHelpers.SatV

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem cptl {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### The item functions and the prefix tests as transducers -/

/-- States of the small transducers. `b`: at the start (or at a pair boundary). `t`, `f`: one
symbol further, after `true` or after `false`. `e`: finished. -/
private inductive IS : Type
  | b | t | f | e
  deriving DecidableEq

private instance : Fintype IS :=
  ⟨{.b, .t, .f, .e}, fun q => by cases q <;> simp⟩

private def hiD : IS → Bool → IS × Option Bool
  | .b, true => (.t, some true)
  | .b, false => (.f, some false)
  | .t, d => (.b, some d)
  | .f, d => (.e, some d)
  | .e, _ => (.e, none)

private theorem hiD_e (l : List Bool) : fstRun hiD (fun _ => none) IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, hiD, ih]

private theorem hiD_run : ∀ s : List Bool, fstRun hiD (fun _ => none) IS.b s = headI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, hiD, headI, hiD_run r]
  | false :: d :: r => by simp [fstRun, hiD, headI, hiD_e]

theorem cpt_headI : CPT headI :=
  fst_polyTime _ _ _ hiD (fun _ => none) IS.b (fun s => (hiD_run s).symm)

private def diD : IS → Bool → IS × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, _ => (.e, none)
  | .e, a => (.e, some a)

private theorem diD_e (l : List Bool) : fstRun diD (fun _ => none) IS.e l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, diD, ih]

private theorem diD_run : ∀ s : List Bool, fstRun diD (fun _ => none) IS.b s = dropI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, diD, dropI, diD_run r]
  | false :: d :: r => by simp [fstRun, diD, dropI, diD_e]

theorem cpt_dropI : CPT dropI :=
  fst_polyTime _ _ _ diD (fun _ => none) IS.b (fun s => (diD_run s).symm)

private def poD : IS → Bool → IS × Option Bool
  | .b, _ => (.t, none)
  | .t, true => (.e, some true)
  | _, _ => (.e, none)

private theorem poD_e (l : List Bool) : fstRun poD (fun _ => none) IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, poD, ih]

private theorem poD_run (s : List Bool) :
    fstRun poD (fun _ => none) IS.b s = bflag (polB s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · rfl
  · cases b <;> simp [fstRun, poD, poD_e, polB, bflag]

private theorem cpt_polF : CPT (fun s => bflag (polB s)) :=
  fst_polyTime _ _ _ poD (fun _ => none) IS.b (fun s => (poD_run s).symm)

private theorem flag_ne (F : List Bool) : sel F [] [true] = bflag (!F.isEmpty) := by
  cases F <;> simp [sel, bflag]

private theorem cpt_eqF {u v : List Bool → List Bool} (hu : CPT u) (hv : CPT v) :
    CPT (fun s => bflag (decide (u s = v s))) := by
  have s : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  exact cptl (cpt_bitFlag (cpt_comp (cpt_pair hu hv) s)) (fun _ => rfl)

/-! ### Membership -/

private theorem cpt_memStep : CPT memStep := by
  have hc : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hr : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hd : CPT (fun s => dropI (unpairB (unpairB s).2).1) := cpt_comp hr cpt_dropI
  have hh : CPT (fun s => headI (unpairB (unpairB s).2).1) := cpt_comp hr cpt_headI
  have he : CPT (fun s => bflag (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))) :=
    cpt_eqF hh hc
  exact cptl (cpt_pairB2 hc (cpt_pairB2 hd (cpt_app2 hfl he))) (fun _ => rfl)

theorem cpt_memB {C W : List Bool → List Bool} (hC : CPT C) (hW : CPT W) :
    CPT (fun s => bflag (memB (C s) (W s))) := by
  have hit : CPT (fun s => memStep^[(W s).length] (pairB (C s) (pairB (W s) []))) :=
    cpt_iterGrow cpt_memStep 3 memStep_length hW (cpt_pairB2 hC (cpt_pairB2 hW (cpt_const [])))
  have hF : CPT (fun s =>
      (unpairB (unpairB (memStep^[(W s).length] (pairB (C s) (pairB (W s) [])))).2).2) :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hit)
  exact cptl (cpt_sel hF (cpt_const []) (cpt_const [true])) (fun s => flag_ne _)

theorem cpt_firstF : CPT (fun s => bflag (s.headD false)) := by
  have h := cpt_comp (cpt_app2 (cpt_const [true]) cpt_id) cpt_polF
  refine cptl h ?_
  intro s
  cases s <;> rfl

end PEqualNP.Outside.SatCodePrimitives
