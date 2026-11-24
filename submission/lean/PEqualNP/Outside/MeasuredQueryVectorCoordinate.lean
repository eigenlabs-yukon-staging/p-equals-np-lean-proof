import PEqualNP.Outside.TrimEncodedFrontier
import PEqualNP.Outside.FrontierFilterByParameter

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x => x)

private theorem tailPacked (n : Nat) (xs : List Word) :
    (fun w : Word => (unpairB w).2)^[n] (encodeFrontier xs) =
      encodeFrontier (xs.drop n) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      have e : (unpairB (encodeFrontier [])).2 = encodeFrontier [] := rfl
      rw [e,ih]
      simp
    | cons x xs =>
      change (fun w : Word => (unpairB w).2)^[n] (unpairB (pairB x (encodeFrontier xs))).2 = _
      rw [unpairB_pairB,ih]
      rfl

private theorem headPacked (xs : List Word) :
    (unpairB (encodeFrontier xs)).1 = xs.headD [] := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change (unpairB (pairB x (encodeFrontier xs))).1 = x
    simp [unpairB_pairB]

/-- Read or remove a unary-indexed record uniformly from an encoded query
vector. Out-of-range reads give the empty word and deletion leaves the list as is. -/
theorem MeasuredQueryVectorCoordinate :
    ∃ (read erase : Word × Word → Word),
      ComputableInPolyTime encodePair (fun x => x) read ∧
      ComputableInPolyTime encodePair (fun x => x) erase ∧
      ∀ (i : Word) (xs : List Word),
        let pack := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        read (i,xs.foldr pack []) = xs[i.length]?.getD [] ∧
        erase (i,xs.foldr pack []) = (xs.eraseIdx i.length).foldr pack [] := by
  obtain ⟨take,takeCpt,takeSpec⟩ := compileDirectionalTrim false
  let drop := fun p : Word × Word => (fun w : Word => (unpairB w).2)^[p.1.length] p.2
  have hraw := cpt_iterLen cpt_unpairB2 (fun s => by have h := unpairB_length s; omega)
    cpt_unpairB1 cpt_unpairB2
  have hd : ComputableInPolyTime encodePair (fun x => x) drop :=
    cpt_fromRaw (f := drop) hraw
  let read := fun p : Word × Word => (unpairB (drop p)).1
  let erase := fun p : Word × Word => take p ++ drop (true::p.1,p.2)
  have hr : ComputableInPolyTime encodePair (fun x => x) read :=
    cpt_comp (f := drop) (g := fun s : Word => (unpairB s).1) hd cpt_unpairB1
  have he : ComputableInPolyTime encodePair (fun x => x) erase := by
    have h := cpt_app2 (cpt_comp cpt_unpairB takeCpt)
      (cpt_comp (cpt_pair (cpt_cons1 true cpt_unpairB1) cpt_unpairB2) hd)
    exact cpt_fromRaw (f := erase) h
  refine ⟨read,erase,hr,he,fun i xs => ?_⟩
  constructor
  · change (unpairB (drop (i,encodeFrontier xs))).1 = _
    rw [show drop (i,encodeFrontier xs) = encodeFrontier (xs.drop i.length)
      from tailPacked _ _ ,headPacked]
    simp only [List.headD_eq_head?_getD,List.head?_drop]
  · have ht : take (i,encodeFrontier xs) = encodeFrontier (xs.take i.length) := takeSpec _ _
    have hs : drop (true::i,encodeFrontier xs) = encodeFrontier (xs.drop (i.length+1)) :=
      tailPacked _ _
    change take (i,encodeFrontier xs) ++ drop (true::i,encodeFrontier xs) =
      encodeFrontier (xs.eraseIdx i.length)
    rw [ht,hs,← encodeFrontier_append_words,List.eraseIdx_eq_take_drop_succ]

end PEqualNP.Outside
