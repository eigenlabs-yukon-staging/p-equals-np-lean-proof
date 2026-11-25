import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Search

private def markers : List Bool → List Bool
  | [] => []
  | [_] => []
  | false :: false :: r => true :: markers r
  | _ :: _ :: r => markers r

private def transition : Ph → Bool → Ph × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, true => (.b, none)
  | .f, false => (.b, some true)

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
    markers (encodeLiteral l ++ r) = markers r := by
  simp [encodeLiteral, List.append_assoc, markers, markers_digits]

private theorem markers_clause (c : Clause) (r : List Bool) :
    markers (encodeClause c ++ r) = true :: markers r := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      have e : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      rw [e, List.append_assoc, markers_literal, ih]

private theorem markers_cnf (φ : CNF) :
    markers (encodeCNF φ) = List.replicate φ.length true := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      have e : encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ := by simp [encodeCNF]
      rw [e, markers_clause, ih, List.length_cons, List.replicate_succ]

/-- Canonical CNF clause count is computable in unary by scanning the clause delimiters. -/
theorem MeasuredCNFClauseCount :
    ∃ count : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) count ∧
      ∀ φ : CNF, count (encodeCNF φ) = List.replicate φ.length true :=
  ⟨markers, fst_polyTime _ _ _ transition (fun _ => none) .b (fun s => (markers_run s).symm), markers_cnf⟩

end PEqualNP.Outside
