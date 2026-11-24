import PEqualNP.Outside.SparsePruningAlgorithm
import PEqualNP.Outside.SparseRepresentativesMachine

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)
local notation "Word" => List Bool

private def immediateYes : Word := pairB [true] []

private def coPrune (f : Word × Word → Word) (s : Word) : Word :=
  let b := (unpairB s).1
  let xs := (unpairB s).2
  let r := representativesMachine f xs
  let pivot := (unpairB xs).1
  let ys := pairB pivot (unpairB r).2
  let within := bflag (decide ((unpairB r).1.length ≤ b.length))
  sel xs (pairB [] []) (sel within immediateYes (pairB [] ys))

private theorem coPrune_polyTime {f : Word × Word → Word}
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    CPT (coPrune f) := by
  have hx := cpt_unpairB2
  have hrep := cpt_comp hx (representativesMachine_polyTime hf)
  have hlen := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 (cpt_unpairB1_1 hrep))
    LenCmp.lenLE_polyTime)
  have hys := cpt_pairB2 (cpt_const [])
    (cpt_pairB2 (cpt_unpairB1_1 hx) (cpt_unpairB2_1 hrep))
  exact bf_cptl (cpt_sel hx (cpt_const (pairB [] []))
    (cpt_sel hlen (cpt_const immediateYes) hys)) (fun _ => rfl)

private theorem reps_eq (f : Word × Word → Word) (a : Word) (xs : List Word) :
    sparseRepresentatives f a xs = sparseListRepresentatives (fun w => f (a,w)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : f (a,x) ∈ xs.map (fun w => f (a,w)) ↔ ∃ y ∈ xs, f (a,y) = f (a,x) :=
      List.mem_map
    simp [sparseRepresentatives, sparseListRepresentatives, h, ih]

private theorem coPrune_spec (f : Word × Word → Word) (A B : Language Bool)
    (dual : ∀ x y, f (x,y) ∈ B ↔ x ∉ A ∧ y ∉ A)
    (b : Nat) (xs : List Word)
    (sparse : ∀ a ∈ xs, ∀ z : Finset Word,
      (∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs, f (a,w) = y) → z.card ≤ b) :
    let out := coPrune f (pairB (un b) (encodeFrontier xs))
    (out = immediateYes ∧ ∃ x ∈ xs, x ∈ A) ∨
      ∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ b + 1 ∧
        out = pairB [] (encodeFrontier ys) ∧
        ((∃ x ∈ ys, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) := by
  classical
  dsimp only
  cases xs with
  | nil =>
    exact Or.inr ⟨[], List.Sublist.slnil, by simp,
      by simp [coPrune, encodeFrontier, unpairB_pairB], Iff.rfl⟩
  | cons a xs =>
    let ys := sparseListRepresentatives (fun w => f (a,w)) xs
    have hne : pairB a (encodeFrontier xs) ≠ [] := encodeFrontier_cons_ne a xs
    have hr : representativesMachine f (pairB a (encodeFrontier xs)) =
        pairB (List.replicate ys.length true) (encodeFrontier ys) := by
      simpa only [reps_eq] using representativesMachine_spec f a xs
    have hsub : ys.Sublist xs := sparseListRepresentatives_sublist _ xs
    by_cases hsize : ys.length ≤ b
    · right
      refine ⟨a :: ys, hsub.cons_cons a, by simp; omega, ?_, ?_⟩
      · change coPrune f (pairB (un b) (pairB a (encodeFrontier xs))) =
          pairB [] (pairB a (encodeFrontier ys))
        simp [coPrune, unpairB_pairB, hr, un_length, sel, bflag, hsize, hne]
      · constructor
        · rintro ⟨w, hw, hwA⟩
          exact ⟨w, (hsub.cons_cons a).subset hw, hwA⟩
        · rintro ⟨w, hw, hwA⟩
          by_cases ha : a ∈ A
          · exact ⟨a, List.mem_cons_self, ha⟩
          · have htail : w ∈ xs := (List.mem_cons.mp hw).resolve_left (fun e => ha (e ▸ hwA))
            have hm := (sparseListRepresentatives_keys (fun z => f (a,z)) xs (f (a,w))).mpr
              (List.mem_map_of_mem htail)
            obtain ⟨u, hu, he⟩ := List.mem_map.mp hm
            have hyes : u ∈ A := by
              by_contra hno
              have hB := (dual a u).mpr ⟨ha,hno⟩
              change f (a,u) = f (a,w) at he
              rw [he] at hB
              exact ((dual a w).mp hB).2 hwA
            exact ⟨u, List.mem_cons_of_mem _ hu, hyes⟩
    · left
      constructor
      · change coPrune f (pairB (un b) (pairB a (encodeFrontier xs))) = immediateYes
        simp [coPrune, unpairB_pairB, hr, un_length, sel, bflag, hsize, hne]
      · by_contra! hno
        let keys := ys.map (fun w => f (a,w))
        have hcard : keys.toFinset.card = ys.length := by
          rw [List.toFinset_card_of_nodup (sparseListRepresentatives_unique _ xs), List.length_map]
        have ha : a ∉ A := hno a List.mem_cons_self
        have hcap := sparse a List.mem_cons_self keys.toFinset (fun y hy => by
          obtain ⟨w, hw, e⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
          have hw' := List.mem_cons_of_mem a (hsub.subset hw)
          exact ⟨e ▸ (dual a w).mpr ⟨ha, hno w hw'⟩, w, hw', e⟩)
        omega

/-- The co-sparse case either certifies existence of a yes candidate immediately
or returns a bounded frontier with the same existential answer. -/
theorem CoSparsePruningMachine (f : Word × Word → Word)
    (hf : ComputableInPolyTime encodePair (fun x => x) f) :
    ∃ run : Word → Word, CPT run ∧
      ∀ (A B : Language Bool), (∀ x y, f (x,y) ∈ B ↔ x ∉ A ∧ y ∉ A) →
      ∀ (b : Nat) (xs : List Word),
        (∀ a ∈ xs, ∀ z : Finset Word,
          (∀ y ∈ z, y ∈ B ∧ ∃ w ∈ xs, f (a,w) = y) → z.card ≤ b) →
        let consWord := fun a b : Word => List.replicate a.length true ++ false :: (a ++ b)
        let out := run (consWord (List.replicate b true) (xs.foldr consWord []))
        (out = consWord [true] [] ∧ ∃ x ∈ xs, x ∈ A) ∨
          ∃ ys : List Word, ys.Sublist xs ∧ ys.length ≤ b + 1 ∧
            out = consWord [] (ys.foldr consWord []) ∧
            ((∃ x ∈ ys, x ∈ A) ↔ ∃ x ∈ xs, x ∈ A) :=
  ⟨coPrune f, coPrune_polyTime hf, coPrune_spec f⟩

end PEqualNP.Outside
