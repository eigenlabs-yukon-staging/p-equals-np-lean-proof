import PEqualNP.Outside.ParameterizedFrontierExpansion
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

theorem cpt_fromRaw {f : Word × Word → Word}
    (hf : CPT (fun s => f (unpairB s))) :
    ComputableInPolyTime encodePair (fun x => x) f := by
  apply bf_cptl (cpt_comp cpt_pairB hf)
  rintro ⟨x,y⟩
  simp [unpairB_pairB]

theorem cpt_fromRawBool {f : Word × Word → Bool}
    (hf : ComputableInPolyTime (fun x => x) Computability.encodeBool
      (fun s => f (unpairB s))) :
    ComputableInPolyTime encodePair Computability.encodeBool f := by
  apply bf_cptl (cpt_comp cpt_pairB hf)
  rintro ⟨x,y⟩
  simp [unpairB_pairB]

def encodedMember (seen key : Word) : Bool :=
  imageLookup (fun p => p.2) (pairB [] (pairB key seen))

theorem encodedMember_cpt {seen key : Word → Word} (hs : CPT seen) (hk : CPT key) :
    ComputableInPolyTime (fun x => x) Computability.encodeBool
      (fun s => encodedMember (seen s) (key s)) :=
  bf_cptl (cpt_comp (cpt_pairB2 (cpt_const []) (cpt_pairB2 hk hs))
    (imageLookup_polyTime cpt_snd)) (fun _ => rfl)

theorem encodedMember_spec (ws : List Word) (key : Word) :
    encodedMember (encodeFrontier ws) key = true ↔ key ∈ ws := by
  change imageLookup (fun p => p.2) (pairB [] (pairB key (ws.foldr pairB []))) = true ↔ _
  rw [imageLookup_spec]
  exact ⟨fun ⟨w,hw,he⟩ => he ▸ hw, fun hx => ⟨key,hx,rfl⟩⟩

private def whenTrue (pred : Word × Word → Bool) (p : Word × Word) : List Word :=
  if pred p then [p.2] else []

private theorem whenTrue_cpt {pred : Word × Word → Bool}
    (hp : ComputableInPolyTime encodePair Computability.encodeBool pred) :
    ComputableInPolyTime encodePair (fun x => x) (fun p => encodeFrontier (whenTrue pred p)) := by
  have hh := cpt_bitFlag (cpt_comp cpt_unpairB hp)
  have hx := cpt_pairB2 cpt_unpairB2 (cpt_const [])
  apply cpt_fromRaw
  refine bf_cptl (cpt_sel hh (cpt_const []) hx) ?_
  intro s
  cases h : pred (unpairB s) <;> simp [whenTrue,h,bflag,encodeFrontier]

private theorem flatMap_whenTrue (pred : Word × Word → Bool) (p : Word) (xs : List Word) :
    xs.flatMap (fun x => whenTrue pred (p,x)) = xs.filter (fun x => pred (p,x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_cons, ih]
    cases h : pred (p,x) <;> simp [whenTrue,h]

/-- A polynomial-time Boolean predicate on a pair yields a measured filter of
an encoded list, with one common parameter supplied alongside the list. -/
theorem FrontierFilterByParameter (pred : Word × Word → Bool)
    (hp : ComputableInPolyTime encodePair Computability.encodeBool pred) :
    ∃ run : Word × Word → Word,
      ComputableInPolyTime encodePair (fun x => x) run ∧
      ∀ (p : Word) (xs : List Word),
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        run (p, xs.foldr consWord []) = (xs.filter (fun x => pred (p,x))).foldr consWord [] := by
  obtain ⟨run, hr, hs⟩ := ParameterizedFrontierExpansion (whenTrue pred) (whenTrue_cpt hp)
  exact ⟨run,hr,fun p xs => by simpa only [flatMap_whenTrue] using hs p xs⟩

end PEqualNP.Outside
