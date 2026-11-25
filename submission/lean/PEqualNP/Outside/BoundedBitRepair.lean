import PEqualNP.Library.L016
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Outside.IndexedWitnessProjection
import PEqualNP.Outside.MeasuredBitFlip

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal

private def byFlips (R : Set (List Bool × List Bool)) (k : ℕ) : Language Bool :=
  {s | ∃ is : List ℕ, is.length = k ∧
    ((unpairB s).1, is.foldl (fun word i => word.modify i Bool.not) (unpairB s).2) ∈ R}

private theorem modify_no_change (word : List Bool) (i : ℕ) (h : word.length ≤ i) :
    word.modify i Bool.not = word := by
  induction word generalizing i with
  | nil => cases i <;> rfl
  | cons b word ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      exact congrArg (b :: ·) (ih i (by simp at h; omega))

private theorem byFlips_mem_P (R : Set (List Bool × List Bool))
    (hR : DecidableInPolyTime encodePair R) (k : ℕ) : byFlips R k ∈ P := by
  induction k with
  | zero =>
      obtain ⟨f, hf, hc⟩ := hR
      refine ⟨fun s => f (unpairB s), fun s => ?_, cpt_comp cpt_unpairB hc⟩
      change (∃ is : List ℕ, is.length = 0 ∧
        ((unpairB s).1, is.foldl (fun word i => word.modify i Bool.not) (unpairB s).2) ∈ R) ↔ _
      rw [← hf]
      simp
  | succ k ih =>
      let Q : Set (List Bool × List Bool) :=
        {z | pairB (unpairB z.1).1 z.2 ∈ byFlips R k}
      have hQ : DecidableInPolyTime encodePair Q := by
        obtain ⟨f, hf, hc⟩ := ih
        exact ⟨fun z => f (pairB (unpairB z.1).1 z.2), fun z => hf _,
          cpt_comp (cpt_comp (cpt_pairG (cpt_comp cpt_fst cpt_unpairB1) cpt_snd) cpt_pairB) hc⟩
      let clock := fun s => true :: (unpairB s).2
      let gen := fun z : List Bool × List Bool => (unpairB z.2).2.modify z.1.length Bool.not
      have hc := cpt_cons1 true cpt_unpairB2
      have hg : ComputableInPolyTime encodePair (fun x : List Bool => x) gen :=
        cpt_comp (cpt_pairG cpt_fst (cpt_comp cpt_snd cpt_unpairB2)) MeasuredBitFlip
      have h := IndexedWitnessProjection Q hQ clock hc gen hg
      have heq : byFlips R (k + 1) =
          {s : List Bool | ∃ i < (clock s).length, (s, gen (List.replicate i true, s)) ∈ Q} := by
        ext s
        let x := (unpairB s).1
        let word := (unpairB s).2
        have hspec (i : ℕ) :
            (s, gen (List.replicate i true, s)) ∈ Q ↔
              ∃ is : List ℕ, is.length = k ∧
                (x, is.foldl (fun word i => word.modify i Bool.not) (word.modify i Bool.not)) ∈ R := by
          change (∃ is : List ℕ, is.length = k ∧
            ((unpairB (pairB x (word.modify (List.replicate i true).length Bool.not))).1,
              is.foldl (fun word i => word.modify i Bool.not)
                (unpairB (pairB x (word.modify (List.replicate i true).length Bool.not))).2) ∈ R) ↔ _
          simp only [List.length_replicate, unpairB_pairB]
        change (∃ is : List ℕ, is.length = k + 1 ∧
            (x, is.foldl (fun word i => word.modify i Bool.not) word) ∈ R) ↔
          ∃ i < word.length + 1, (s, gen (List.replicate i true, s)) ∈ Q
        constructor
        · rintro ⟨is, hk, hR'⟩
          cases is with
          | nil => simp at hk
          | cons i is =>
            have hk' : is.length = k := by simpa using hk
            refine ⟨min i word.length, by omega, (hspec _).mpr ⟨is, hk', ?_⟩⟩
            change (x, is.foldl (fun word i => word.modify i Bool.not)
              (word.modify i Bool.not)) ∈ R at hR'
            by_cases hi : i ≤ word.length
            · simpa [Nat.min_eq_left hi] using hR'
            · have hle : word.length ≤ i := by omega
              rw [Nat.min_eq_right hle, modify_no_change word word.length le_rfl]
              rwa [modify_no_change word i hle] at hR'
        · rintro ⟨i, _, hi⟩
          obtain ⟨is, hk, hR'⟩ := (hspec i).mp hi
          exact ⟨i :: is, by simp [hk], hR'⟩
      rwa [heq]

/-- A polynomial-time predictor can be repaired by a fixed number of arbitrary bit flips. -/
theorem BoundedBitRepair
    (R : Set (List Bool × List Bool)) (hR : DecidableInPolyTime encodePair R)
    (predict : List Bool → List Bool)
    (hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) predict)
    (k : ℕ) :
    {x : List Bool | ∃ is : List ℕ, is.length = k ∧
      (x, is.foldl (fun word i => word.modify i Bool.not) (predict x)) ∈ R} ∈ P := by
  apply L016 _ (byFlips R k) _ (byFlips_mem_P R hR k)
  refine ⟨fun x => pairB x (predict x), cpt_pairB2 cpt_id hp, fun x => ?_⟩
  change (∃ is : List ℕ, is.length = k ∧
      (x, is.foldl (fun word i => word.modify i Bool.not) (predict x)) ∈ R) ↔
    (∃ is : List ℕ, is.length = k ∧
      ((unpairB (pairB x (predict x))).1,
        is.foldl (fun word i => word.modify i Bool.not) (unpairB (pairB x (predict x))).2) ∈ R)
  simp only [unpairB_pairB]

end PEqualNP.Outside
