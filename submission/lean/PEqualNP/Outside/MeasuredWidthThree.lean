import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV

private def width (n : ℕ) : List Bool → Bool
  | [] => true
  | [_] => false
  | true :: _ :: r => width n r
  | false :: false :: r => width 0 r
  | false :: true :: r => decide (n < 3) && width (n+1) r

private def widthTransition : Option (Fin 4 × Ph) → Bool → Option (Fin 4 × Ph) × Option Bool
  | none, _ => (none, none)
  | some (n, .b), true => (some (n, .t), none)
  | some (n, .b), false => (some (n, .f), none)
  | some (n, .t), _ => (some (n, .b), none)
  | some (_, .f), false => (some (0, .b), none)
  | some (n, .f), true =>
      (if h : n.val < 3 then some (⟨n.val + 1, by omega⟩, .b) else none, none)

private def widthFinish : Option (Fin 4 × Ph) → Option Bool
  | some (_, .b) => some true
  | _ => none

private theorem width_dead (r : List Bool) : fstRun widthTransition widthFinish none r = [] := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [fstRun, widthTransition, ih]

private theorem width_run : ∀ (r : List Bool) (n : ℕ) (hn : n < 4),
    fstRun widthTransition widthFinish (some (⟨n, hn⟩, .b)) r =
      (if width n r then [true] else [])
  | [], _, _ => rfl
  | [b], _, _ => by cases b <;> rfl
  | true :: b :: r, n, hn => by
      change fstRun widthTransition widthFinish (some (⟨n, hn⟩, .b)) r = _
      rw [width]
      exact width_run r n hn
  | false :: false :: r, n, hn => by
      change fstRun widthTransition widthFinish (some (0, .b)) r = _
      rw [width]
      exact width_run r 0 (by omega)
  | false :: true :: r, n, hn => by
      by_cases h : n < 3
      · simpa [fstRun, widthTransition, width, h] using width_run r (n+1) (by omega)
      · simp [fstRun, widthTransition, width, h, width_dead]

private theorem width_digits (n : ℕ) (ds r : List Bool) :
    width n ((ds.flatMap fun d => [true,d]) ++ r) = width n r := by
  induction ds with
  | nil => rfl
  | cons b ds ih => simp [width, ih]

private theorem width_literal (n : ℕ) (l : Literal) (r : List Bool) :
    width n (encodeLiteral l ++ r) = (decide (n < 3) && width (n+1) r) := by
  have h : encodeLiteral l ++ r =
      true :: l.2 :: ((l.1.bits.flatMap fun d => [true,d]) ++ false :: true :: r) := by
    simp [encodeLiteral]
  rw [h, width, width_digits, width]

private theorem width_clause (r : List Bool) : ∀ (c : Clause) (n : ℕ), n ≤ 3 →
    width n (encodeClause c ++ r) = (decide (n + c.length ≤ 3) && width 0 r)
  | [], n, hn => by simp [encodeClause, width, hn]
  | l :: c, n, hn => by
      have h : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
        simp [encodeClause]
      rw [h, width_literal]
      by_cases hl : n < 3
      · rw [width_clause r c (n+1) (by omega)]
        have he : (n + 1 + c.length ≤ 3) ↔ (n + (l :: c).length ≤ 3) := by
          simp only [List.length_cons]
          omega
        simp only [hl, decide_true, Bool.true_and, decide_eq_decide.mpr he]
      · have he : ¬ n + (l :: c).length ≤ 3 := by
          simp only [List.length_cons]
          omega
        rw [decide_eq_false hl, decide_eq_false he]
        rfl

private theorem width_cnf (φ : CNF) : width 0 (encodeCNF φ) = true ↔ IsKCNF 3 φ := by
  induction φ with
  | nil => simp [encodeCNF, width, IsKCNF]
  | cons c φ ih =>
      change width 0 (encodeClause c ++ encodeCNF φ) = true ↔ _
      rw [width_clause _ _ _ (by omega)]
      simp [ih, IsKCNF]

/-- A measured guard recognizes the exact well-formed canonical 3-CNF language. -/
theorem MeasuredWidthThree :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧ IsKCNF 3 φ} ∈ P := by
  have hw : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => if width 0 x then [true] else []) :=
    fst_polyTime _ _ _ widthTransition widthFinish (some (0, .b))
      (fun s => (width_run s 0 (by omega)).symm)
  have hvalid := PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF
  have hflag := cpt_sel hvalid (cpt_const []) hw
  have hc := cpt_comp hflag bf_cpt_neL
  have hbool (s : List Bool) : (!(sel (bflag (wfB s)) [] (if width 0 s then [true] else [])).isEmpty) =
      (wfB s && width 0 s) := by
    cases wfB s <;> cases width 0 s <;> rfl
  have hfull : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => wfB s && width 0 s) := by
    have h : (fun s : List Bool =>
      !(sel (bflag (wfB s)) [] (if width 0 s then [true] else [])).isEmpty) =
      (fun s => wfB s && width 0 s) := funext hbool
    rwa [← h]
  refine ⟨_, fun s => ?_, hfull⟩
  change (∃ φ : CNF, encodeCNF φ = s ∧ IsKCNF 3 φ) ↔ (wfB s && width 0 s) = true
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨φ, rfl, hφ⟩
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩, (width_cnf φ).mpr hφ⟩
  · rintro ⟨hwell, hwidth⟩
    obtain ⟨φ, rfl⟩ := (wfB_iff _).mp hwell
    exact ⟨φ, rfl, (width_cnf φ).mp hwidth⟩

end PEqualNP.Outside
