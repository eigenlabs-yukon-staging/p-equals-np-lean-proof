import PEqualNP.Library.Machines.ConstList
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.Transducer

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines

private theorem scan_polyTime :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x => x.any id) := by
  let step := fun (q a : Bool) => (q || a, (none : Option Bool))
  let finish := fun q : Bool => some q
  refine fst_polyTime _ _ _ step finish false ?_
  have run (xs : List Bool) (q : Bool) :
      fstRun step finish q xs = [q || xs.any id] := by
    induction xs generalizing q with
    | nil => simp [fstRun, finish]
    | cons a xs ih =>
      simp [fstRun, step, ih, Bool.or_assoc]
  intro xs
  simp [run, Computability.encodeBool]

private theorem sameOutput {β γ : Type} {eb : β → List Bool} {ec : γ → List Bool}
    {f : List Bool → β} {g : List Bool → γ}
    (hf : ComputableInPolyTime (fun x => x) eb f)
    (h : ∀ x, ec (g x) = eb (f x)) :
    ComputableInPolyTime (fun x => x) ec g := by
  obtain ⟨m⟩ := hf
  exact ⟨⟨m.toTM2ComputableAux, m.time, fun x => by rw [h]; exact m.outputsFun x⟩⟩

private theorem disjoin {f g : List Bool → Bool}
    (hf : ComputableInPolyTime (fun x => x) Computability.encodeBool f)
    (hg : ComputableInPolyTime (fun x => x) Computability.encodeBool g) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool (fun x => f x || g x) := by
  have hf' : ComputableInPolyTime (fun x => x) (fun x => x) (fun x => [f x]) :=
    sameOutput hf (fun _ => rfl)
  have hg' : ComputableInPolyTime (fun x => x) (fun x => x) (fun x => [g x]) :=
    sameOutput hg (fun _ => rfl)
  have h := cpt_comp (cpt_comp (cpt_pair hf' hg') cpt_append) scan_polyTime
  simpa using h

private theorem any_polyTime (f : List Bool → List Bool → Bool)
    (hf : ∀ w, ComputableInPolyTime (fun x => x) Computability.encodeBool (fun x => f x w))
    (ws : List (List Bool)) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool
      (fun x => ws.any (f x)) := by
  induction ws with
  | nil => exact sameOutput (constList_polyTime [false]) (fun _ => rfl)
  | cons w ws ih => exact disjoin (hf w) ih

/-- An arbitrary input-independent finite collection of candidate witnesses can be
searched in deterministic polynomial time using the original pair verifier. -/
theorem FiniteWitnessSearch (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) (ws : List (List Bool)) :
    ({x : List Bool | ∃ w ∈ ws, (x, w) ∈ R} : Language Bool) ∈ P := by
  obtain ⟨verify, spec, hverify⟩ := hR
  refine ⟨fun x => ws.any (fun w => verify (x, w)), ?_, ?_⟩
  · intro x
    simp only [Set.mem_ofPred_eq, List.any_eq_true, spec]
  · exact any_polyTime (fun x w => verify (x, w))
      (fun w => cpt_comp (cpt_pair cpt_id (constList_polyTime w)) hverify) ws

end PEqualNP.Outside
