import PEqualNP.Library.SearchHelpers.TableauStepWLoop

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

private def packGroups (groups : List (List Bool × List Bool × List Bool)) : List Bool :=
  groups.foldr (fun group rest => pairB (pairB group.1 (pairB group.2.1 group.2.2)) rest) []

private def selectWord (group seed : List Bool) : List Bool :=
  if seed.headD false then (unpairB group).1
  else if seed.tail.headD false then (unpairB (unpairB group).2).1
  else (unpairB (unpairB group).2).2

private theorem cpt_selectWord {group seed : List Bool → List Bool}
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) group)
    (hs : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) seed) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => selectWord (group s) (seed s)) := by
  have hrest := cpt_unpairB2_1 hg
  have htail := cpt_sel (cpt_hd1 (cpt_tail1 hs)) (cpt_unpairB2_1 hrest) (cpt_unpairB1_1 hrest)
  have hsel := cpt_sel (cpt_hd1 hs) htail (cpt_unpairB1_1 hg)
  refine cptE hsel (fun s => ?_)
  unfold selectWord
  cases seed s with
  | nil => rfl
  | cons b seed =>
      cases b with
      | true => rfl
      | false => cases seed with
        | nil => rfl
        | cons b seed => cases b <;> rfl

private theorem selectWord_length (group seed : List Bool) : (selectWord group seed).length ≤ group.length := by
  have h1 := unpairB_length group
  have h2 := unpairB_length (unpairB group).2
  unfold selectWord
  split
  · omega
  · split <;> omega

private def selectStep (s : List Bool) : List Bool :=
  let groups := (unpairB s).1
  let seed := (unpairB (unpairB s).2).1
  let out := (unpairB (unpairB s).2).2
  if groups = [] then s
  else pairB (unpairB groups).2 (pairB seed.tail.tail
    (out ++ selectWord (unpairB groups).1 seed))

private theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) selectStep := by
  have hg := cpt_unpairB1
  have hs := cpt_unpairB1_1 cpt_unpairB2
  have ho := cpt_unpairB2_1 cpt_unpairB2
  have hc := cpt_selectWord (cpt_unpairB1_1 hg) hs
  exact cpt_sel hg cpt_id (cpt_pairB2 (cpt_unpairB2_1 hg)
    (cpt_pairB2 (cpt_tail1 (cpt_tail1 hs)) (cpt_app2 ho hc)))

private theorem step_length (s : List Bool) : (selectStep s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB s).1
  have h4 := selectWord_length (unpairB (unpairB s).1).1 (unpairB (unpairB s).2).1
  have h5 : (unpairB (unpairB s).2).1.tail.tail.length ≤ (unpairB (unpairB s).2).1.length := by simp <;> omega
  dsimp only [selectStep]
  split
  · omega
  · simp only [pairB_length, List.length_append]
    omega

private def selected : List (List Bool × List Bool × List Bool) → List Bool → List Bool
  | [], _ => []
  | (a,b,c) :: groups, seed =>
      (if seed.headD false then a else if seed.tail.headD false then b else c) ++
      selected groups seed.tail.tail

private theorem run_groups (groups : List (List Bool × List Bool × List Bool))
    (seed out : List Bool) (n : ℕ) (hn : groups.length ≤ n) :
    (unpairB (unpairB (selectStep^[n] (pairB (packGroups groups) (pairB seed out)))).2).2 =
      out ++ selected groups seed := by
  induction n generalizing groups seed out with
  | zero =>
      have hgroup : groups = [] := List.length_eq_zero_iff.mp (by omega)
      subst groups
      simp [packGroups, selected, unpairB_pairB]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases groups with
      | nil =>
          have hstep : selectStep (pairB (packGroups []) (pairB seed out)) =
              pairB (packGroups []) (pairB seed out) := by simp [selectStep, packGroups, unpairB_pairB]
          rw [hstep, ih _ _ _ (by simp)]
      | cons group groups =>
          rcases group with ⟨a,b,c⟩
          let g := pairB a (pairB b c)
          have hpack : packGroups ((a,b,c) :: groups) = pairB g (packGroups groups) := rfl
          have hne : pairB g (packGroups groups) ≠ [] := by
            intro h
            have hl := pairB_length g (packGroups groups)
            rw [h] at hl
            simp at hl
          have hs : selectStep (pairB (packGroups ((a,b,c) :: groups)) (pairB seed out)) =
              pairB (packGroups groups)
                (pairB seed.tail.tail (out ++ (if seed.headD false then a
                  else if seed.tail.headD false then b else c))) := by
            rw [hpack]
            simp only [selectStep, unpairB_pairB, ite_eq_right hne, selectWord, g]
          rw [hs, ih _ _ _ (by simpa using hn), selected, List.append_assoc]

private theorem packGroups_length (groups : List (List Bool × List Bool × List Bool)) :
    groups.length ≤ (packGroups groups).length := by
  induction groups with
  | nil => simp [packGroups]
  | cons group groups ih =>
      rcases group with ⟨a,b,c⟩
      change groups.length + 1 ≤ (pairB (pairB a (pairB b c)) (packGroups groups)).length
      rw [pairB_length]
      omega

private theorem selected_indexed (groups : List (List Bool × List Bool × List Bool)) (seed : List Bool) :
    selected groups seed =
      (List.range groups.length).flatMap (fun i =>
        let group := groups[i]?.getD ([],[],[])
        if seed.getD (2*i) false then group.1
        else if seed.getD (2*i+1) false then group.2.1 else group.2.2) := by
  induction groups generalizing seed with
  | nil => simp [selected]
  | cons group groups ih =>
      rcases group with ⟨a,b,c⟩
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [selected, ih, List.getElem?_cons_zero, Option.getD_some, Nat.mul_zero,
        Nat.zero_add, List.headD_eq_getD]
      congr 1
      · simp [List.getD, List.getElem?_tail] <;> rfl
      · congr 1
        funext i
        simp [List.getD, List.getElem?_tail, Nat.mul_succ, Nat.add_assoc]

/-- Select one bit-string alternative per triple with two seed bits per group. -/
theorem MeasuredTripleSelections :
    ∃ select : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) select ∧
      ∀ (groups : List (List Bool × List Bool × List Bool)) (seed : List Bool),
        select (groups.foldr (fun group rest =>
          let bc := List.replicate group.2.1.length true ++ false :: (group.2.1 ++ group.2.2)
          let abc := List.replicate group.1.length true ++ false :: (group.1 ++ bc)
          List.replicate abc.length true ++ false :: (abc ++ rest)) [], seed) =
          (List.range groups.length).flatMap (fun i =>
            let group := groups[i]?.getD ([],[],[])
            if seed.getD (2*i) false then group.1
            else if seed.getD (2*i+1) false then group.2.1 else group.2.2) := by
  let start := fun s => pairB (unpairB s).1 (pairB (unpairB s).2 [])
  let output := fun s => (unpairB (unpairB
    (selectStep^[(unpairB s).1.length] (start s))).2).2
  have hstart := cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_unpairB2 (cpt_const []))
  have hout : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) output :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow cpt_step 2 step_length cpt_unpairB1 hstart))
  refine ⟨fun p => output (pairB p.1 p.2), cpt_comp cpt_pairB hout, fun groups seed => ?_⟩
  change output (pairB (packGroups groups) seed) = _
  simp only [output, start, unpairB_pairB]
  rw [run_groups groups seed [] _ (packGroups_length groups), List.nil_append]
  exact selected_indexed groups seed

end PEqualNP.Outside
