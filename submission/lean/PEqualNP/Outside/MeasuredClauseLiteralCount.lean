import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Search

private def markers : List Bool → List Bool
  | [] => []
  | [_] => []
  | false :: true :: r => true :: markers r
  | _ :: _ :: r => markers r

private def transition : Ph → Bool → Ph × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, true => (.b, some true)
  | .f, false => (.b, none)

private theorem markers_run : ∀ r : List Bool,
    fstRun transition (fun _ => none) .b r = markers r
  | [] => rfl
  | [b] => by cases b <;> rfl
  | false :: false :: r => by simp [fstRun, transition, markers, markers_run r]
  | false :: true :: r => by simp [fstRun, transition, markers, markers_run r]
  | true :: b :: r => by simp [fstRun, transition, markers, markers_run r]

private theorem markers_digits (ds r : List Bool) :
    markers ((ds.flatMap fun d => [true,d]) ++ r) = markers r := by
  induction ds with
  | nil => rfl
  | cons b ds ih => simp [markers, ih]

private theorem markers_literal (l : Literal) (r : List Bool) :
    markers (encodeLiteral l ++ r) = true :: markers r := by
  simp [encodeLiteral, List.append_assoc, markers, markers_digits]

private theorem markers_clause (c : Clause) :
    markers (encodeClause c) = List.replicate c.length true := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      have e : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      rw [e, markers_literal, ih, List.length_cons, List.replicate_succ]

/-- Count the literals of an encoded clause by scanning its literal terminators. -/
theorem MeasuredClauseLiteralCount :
    ∃ count : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) count ∧
      ∀ c : Clause, count (encodeClause c) = List.replicate c.length true :=
  ⟨markers, fst_polyTime _ _ _ transition (fun _ => none) .b (fun s => (markers_run s).symm), markers_clause⟩

end PEqualNP.Outside
