import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

local notation "Word" => List Bool
local notation "CPT" => ComputableInPolyTime (fun x : List Bool => x) (fun x => x)

private def headFlag (w : Word) : Word := bflag (w.headD false)

private def headStep (done b : Bool) : Bool × Option Bool :=
  (true, if !done && b then some true else none)

private theorem headFlag_cpt : CPT headFlag := by
  have finish (xs : Word) : fstRun headStep (fun _ => none) true xs = [] := by
    induction xs with
    | nil => rfl
    | cons b xs ih => simp [fstRun, headStep, ih]
  apply fst_polyTime _ _ _ headStep (fun _ => none) false
  intro x
  cases x with
  | nil => rfl
  | cons b bs => cases b <;> simp [headFlag, fstRun, headStep, finish, bflag]

theorem wordHead_polyTime :
    ComputableInPolyTime (fun x : Word => x) Computability.encodeBool (fun w => w.headD false) := by
  refine bf_cptl (cpt_comp headFlag_cpt bf_cpt_neL) ?_
  intro w
  cases w with
  | nil => simp [headFlag, bflag]
  | cons b bs => cases b <;> simp [headFlag, bflag]

private def lexFinal (b : Bool) : Word := pairB [b] []

private def lexStep (s : Word) : Word :=
  let tag := (unpairB s).1
  let raw := (unpairB s).2
  let x := (unpairB raw).1
  let y := (unpairB raw).2
  let mismatch := bflag (decide (headFlag x = headFlag y))
  let tails := pairB [] (pairB x.tail y.tail)
  let unequal := sel (headFlag x) (lexFinal true) (lexFinal false)
  let both := sel mismatch unequal tails
  let nonemptyX := sel y (lexFinal false) both
  let emptyX := sel y (lexFinal false) (lexFinal true)
  sel tag (sel x emptyX nonemptyX) s

private theorem lexStep_cpt : CPT lexStep := by
  have htag := cpt_unpairB1
  have hx := cpt_unpairB1_1 cpt_unpairB2
  have hy := cpt_unpairB2_1 cpt_unpairB2
  have hheadX := cpt_comp hx headFlag_cpt
  have hheadY := cpt_comp hy headFlag_cpt
  have hcompare := PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF hheadX hheadY
  have ht := cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_comp hx cpt_tail) (cpt_comp hy cpt_tail))
  have hnegative := cpt_const (lexFinal false)
  have hpositive := cpt_const (lexFinal true)
  have hneq := cpt_sel hheadX hpositive hnegative
  exact bf_cptl (cpt_sel htag
    (cpt_sel hx (cpt_sel hy hnegative hpositive) (cpt_sel hy hnegative (cpt_sel hcompare hneq ht)))
    cpt_id) (fun _ => rfl)

private theorem lexStep_size (s : Word) : (lexStep s).length ≤ s.length + 3 := by
  have h₁ := unpairB_length s
  have h₂ := unpairB_length (unpairB s).2
  unfold lexStep
  dsimp only
  apply sel_length
  · apply sel_length
    · apply sel_length <;> simp [lexFinal, pairB_length]
    · apply sel_length
      · simp [lexFinal, pairB_length]
      · apply sel_length
        · apply sel_length <;> simp [lexFinal, pairB_length]
        · simp only [pairB_length, List.length_nil, Nat.mul_zero, Nat.zero_add, List.length_tail]
          omega
  · omega

private theorem lexFinal_fixed (b : Bool) : lexStep (lexFinal b) = lexFinal b := by
  simp [lexStep, lexFinal, unpairB_pairB]

private def smallBit (a b : Bool) : Bool := !a && b

private theorem lexIter_spec (x : Word) :
    ∀ (y : Word) (k : Nat), x.length < k →
      lexStep^[k] (pairB [] (pairB x y)) = lexFinal (List.lex x y smallBit) := by
  induction x with
  | nil =>
    intro y k hk
    cases k with
    | zero => omega
    | succ k =>
      have hs : lexStep (pairB [] (pairB [] y)) = lexFinal (List.lex [] y smallBit) := by
        cases y <;> simp [lexStep, unpairB_pairB, List.nil_lex_nil]
      rw [Function.iterate_succ_apply, hs, Function.iterate_fixed (lexFinal_fixed _) k]
  | cons a as ih =>
    intro y k hk
    cases k with
    | zero => omega
    | succ k =>
      have hlt : as.length < k := by simp only [List.length_cons] at hk; omega
      rw [Function.iterate_succ_apply]
      cases y with
      | nil =>
        have hs : lexStep (pairB [] (pairB (a::as) [])) = lexFinal false := by
          simp [lexStep, unpairB_pairB]
        rw [hs, Function.iterate_fixed (lexFinal_fixed _) k]
        simp
      | cons b bs =>
        cases a <;> cases b
        · simpa [lexStep, unpairB_pairB, headFlag, bflag, smallBit] using ih bs k hlt
        · have hs : lexStep (pairB [] (pairB (false::as) (true::bs))) = lexFinal true := by
            simp [lexStep, unpairB_pairB, headFlag, bflag]
          rw [hs, Function.iterate_fixed (lexFinal_fixed _) k]
          simp [smallBit]
        · have hs : lexStep (pairB [] (pairB (true::as) (false::bs))) = lexFinal false := by
            simp [lexStep, unpairB_pairB, headFlag, bflag]
          rw [hs, Function.iterate_fixed (lexFinal_fixed _) k]
          simp [smallBit]
        · simpa [lexStep, unpairB_pairB, headFlag, bflag, smallBit] using ih bs k hlt

/-- Strict lexicographic comparison of arbitrary binary words on the reference tagged
pair alphabet. The scan keeps an explicit terminal comparison flag. -/
theorem LexicographicWordCompare :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : Word × Word => p.1.lex p.2 (fun a b => !a && b)) := by
  let run := fun s : Word => lexStep^[s.length + 1] (pairB [] s)
  have hr : CPT run := bf_cptl
    (cpt_iterGrow lexStep_cpt 3 lexStep_size (cpt_cons1 true cpt_id)
      (cpt_pairB2 (cpt_const []) cpt_id)) (fun _ => rfl)
  have hread := cpt_comp (cpt_comp (cpt_unpairB1_1 hr) headFlag_cpt) bf_cpt_neL
  have h := cpt_comp cpt_pairB hread
  apply bf_cptl h
  rintro ⟨x,y⟩
  have hl : x.length < (pairB x y).length + 1 := by rw [pairB_length]; omega
  have he := lexIter_spec x y ((pairB x y).length + 1) hl
  simp only [run, he, lexFinal, unpairB_pairB, headFlag, List.headD_cons]
  change (!(bflag (List.lex x y smallBit)).isEmpty) = List.lex x y smallBit
  cases List.lex x y smallBit <;> rfl

end PEqualNP.Outside
