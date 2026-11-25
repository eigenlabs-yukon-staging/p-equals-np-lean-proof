import PEqualNP.Library.SearchHelpers.TwoSatCPT

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Search

private abbrev Raw := List Bool

private def payload : ℕ → Raw → Raw
  | 0, _ => []
  | n+1, s => sel (hd s) [] (headI s ++ negI (headI s) ++ payload n (dropI s))

private theorem payload_cpt (n : ℕ) :
    ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (payload n) := by
  induction n with
  | zero => exact cpt_const []
  | succ n ih =>
    exact cpt_sel cpt_hd (cpt_const [])
      (cpt_app2 (cpt_app2 cpt_headI (cpt_negI cpt_headI)) (cpt_comp cpt_dropI ih))

private def signed (c : Clause) : Clause := c.flatMap (fun l => [l,neg l])

private theorem payload_spec (n : ℕ) (c : Clause) :
    payload n (encodeClause c) = (signed (c.take n)).flatMap encodeLiteral := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases c with
    | nil => rfl
    | cons l c =>
      have he : encodeClause (l::c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      have hh : hd (encodeLiteral l ++ encodeClause c) ≠ [] := by simp [hd,encodeLiteral_eq]
      simp only [payload,he,sel,hh,ite_false,headI_lit,dropI_lit,negI_lit,ih,List.take_succ_cons,
        signed,List.flatMap_cons,List.flatMap_nil,List.flatMap_append,List.append_nil,List.nil_append,List.append_assoc]

/-- Keep at most the first m literals of a suffix and emit both
polarities for every retained variable. -/
theorem MeasuredSignedLiteralWindow (m : ℕ) :
    ∃ make : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) make ∧
      ∀ c : Clause, make (encodeClause c) =
        encodeClause ((c.take m).flatMap (fun l => [l,(l.1,!l.2)])) := by
  refine ⟨fun s => payload m s ++ [false,false],cpt_app2 (payload_cpt m) (cpt_const [false,false]),fun c => ?_⟩
  change payload m (encodeClause c) ++ [false,false] = _
  rw [payload_spec]
  rfl

end PEqualNP.Outside
