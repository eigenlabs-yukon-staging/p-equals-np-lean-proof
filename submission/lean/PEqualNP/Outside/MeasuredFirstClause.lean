import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Search

private inductive Mode
  | boundary | afterTrue | afterFalse | suffix
  deriving DecidableEq

private instance : Fintype Mode :=
  ⟨{.boundary, .afterTrue, .afterFalse, .suffix}, fun q => by cases q <;> simp⟩

private def step : Mode → Bool → Mode × Option (Bool ⊕ Bool)
  | .boundary, true => (.afterTrue, some (.inl true))
  | .boundary, false => (.afterFalse, some (.inl false))
  | .afterTrue, b => (.boundary, some (.inl b))
  | .afterFalse, true => (.boundary, some (.inl true))
  | .afterFalse, false => (.suffix, some (.inl false))
  | .suffix, b => (.suffix, some (.inr b))

private def splitClause : List Bool → List Bool × List Bool
  | [] => ([], [])
  | [b] => ([b], [])
  | false :: false :: r => ([false,false], r)
  | a :: b :: r => (a :: b :: (splitClause r).1, (splitClause r).2)

private theorem suffix_run (r : List Bool) :
    fstRun step (fun _ => none) .suffix r = r.map Sum.inr := by
  induction r with
  | nil => rfl
  | cons b r ih => simp [fstRun, step, ih]

private theorem split_run : ∀ r : List Bool,
    fstRun step (fun _ => none) .boundary r = encodePair (splitClause r)
  | [] => rfl
  | [b] => by cases b <;> rfl
  | false :: false :: r => by simp [fstRun, step, suffix_run, splitClause, encodePair]
  | false :: true :: r => by simp [fstRun, step, splitClause, encodePair, split_run r]
  | true :: b :: r => by simp [fstRun, step, splitClause, encodePair, split_run r]

private theorem prepend_digits (digits r : List Bool) :
    splitClause ((digits.flatMap fun d => [true,d]) ++ r) =
      ((digits.flatMap fun d => [true,d]) ++ (splitClause r).1, (splitClause r).2) := by
  induction digits with
  | nil => simp
  | cons b digits ih => simp [splitClause, ih]

private theorem literal_continue (l : Literal) (r : List Bool) :
    splitClause (encodeLiteral l ++ r) = (encodeLiteral l ++ (splitClause r).1, (splitClause r).2) := by
  simp [encodeLiteral, List.append_assoc, splitClause, prepend_digits]

private theorem split_clause (c : Clause) (r : List Bool) :
    splitClause (encodeClause c ++ r) = (encodeClause c, r) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      have he : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      rw [he, List.append_assoc, literal_continue, ih]

private theorem split_reassembles : ∀ s : List Bool,
    (splitClause s).1 ++ (splitClause s).2 = s
  | [] => rfl
  | [b] => by cases b <;> rfl
  | false :: false :: r => rfl
  | false :: true :: r => by simp [splitClause, split_reassembles r]
  | true :: b :: r => by simp [splitClause, split_reassembles r]

theorem measuredFirstClause_reassembles :
    ∃ split : List Bool → List Bool × List Bool,
      ComputableInPolyTime (fun x : List Bool => x) encodePair split ∧
      (∀ s, (split s).1 ++ (split s).2 = s) ∧
      ∀ (c : Clause) (tail : List Bool),
        split (encodeClause c ++ tail) = (encodeClause c, tail) :=
  ⟨splitClause, fst_polyTime _ _ _ step (fun _ => none) .boundary (fun s => (split_run s).symm),
    split_reassembles, split_clause⟩

/-- The first clause of a canonical formula can be separated from the raw suffix in linear time. -/
theorem MeasuredFirstClause :
    ∃ split : List Bool → List Bool × List Bool,
      ComputableInPolyTime (fun x : List Bool => x) encodePair split ∧
      split [] = ([],[]) ∧
      ∀ (c : Clause) (tail : List Bool),
        split (encodeClause c ++ tail) = (encodeClause c, tail) := by
  exact ⟨splitClause,
    fst_polyTime _ _ _ step (fun _ => none) .boundary (fun s => (split_run s).symm),
    rfl, split_clause⟩

end PEqualNP.Outside
