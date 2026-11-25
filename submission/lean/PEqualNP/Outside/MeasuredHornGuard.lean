import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library
open PEqualNP.Library.Machines
open PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Search

private def check (inside : Bool) (n : ℕ) : List Bool → Bool
  | [] => true
  | [_] => false
  | true :: b :: r =>
      if inside then check true n r
      else if b then decide (n < 1) && check true (n+1) r
      else check true n r
  | false :: true :: r => check false n r
  | false :: false :: r => check false 0 r

private def trans : Option (Bool × Fin 2 × Ph) → Bool →
    Option (Bool × Fin 2 × Ph) × Option Bool
  | none,_ => (none,none)
  | some (inside,n,.b),true => (some (inside,n,.t),none)
  | some (inside,n,.b),false => (some (inside,n,.f),none)
  | some (true,n,.t),_ => (some (true,n,.b),none)
  | some (false,n,.t),false => (some (true,n,.b),none)
  | some (false,n,.t),true =>
      (if h : n.val < 1 then some (true,⟨n.val+1,by omega⟩,.b) else none,none)
  | some (_,n,.f),true => (some (false,n,.b),none)
  | some (_,_,.f),false => (some (false,0,.b),none)

private def finish : Option (Bool × Fin 2 × Ph) → Option Bool
  | some (_,_,.b) => some true
  | _ => none

private theorem dead_run (r : List Bool) : fstRun trans finish none r = [] := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [fstRun,trans,ih]

private theorem check_run : ∀ (r : List Bool) (inside : Bool) (n : ℕ) (hn : n < 2),
    fstRun trans finish (some (inside,⟨n,hn⟩,.b)) r = bflag (check inside n r)
  | [], inside, n, hn => by cases inside <;> rfl
  | [b], inside, n, hn => by cases inside <;> cases b <;> rfl
  | true :: b :: r, true, n, hn => by
      change fstRun trans finish (some (true,⟨n,hn⟩,.b)) r = _
      rw [check]
      exact check_run r true n hn
  | true :: false :: r, false, n, hn => by
      change fstRun trans finish (some (true,⟨n,hn⟩,.b)) r = _
      rw [check]
      exact check_run r true n hn
  | true :: true :: r, false, n, hn => by
      by_cases h : n < 1
      · simp [fstRun,trans,check,h,check_run r true (n+1) (by omega)]
      · simp [fstRun,trans,check,h,dead_run,bflag]
  | false :: true :: r, inside, n, hn => by
      change fstRun trans finish (some (false,⟨n,hn⟩,.b)) r = _
      rw [check]
      exact check_run r false n hn
  | false :: false :: r, inside, n, hn => by
      change fstRun trans finish (some (false,0,.b)) r = _
      rw [check]
      exact check_run r false 0 (by omega)

private theorem digits (n : ℕ) (ds r : List Bool) :
    check true n ((ds.flatMap fun d => [true,d]) ++ r) = check true n r := by
  induction ds with
  | nil => rfl
  | cons a ds ih => simp [check,ih]

private theorem literal (n : ℕ) (l : Literal) (r : List Bool) :
    check false n (encodeLiteral l ++ r) =
      (if l.2 then decide (n < 1) && check false (n+1) r else check false n r) := by
  obtain ⟨i,b⟩ := l
  have he : encodeLiteral (i,b) ++ r =
      true :: b :: ((i.bits.flatMap fun d => [true,d]) ++ false :: true :: r) := by
    simp [encodeLiteral]
  rw [he]
  cases b <;> simp [check,digits]

private theorem clause (r : List Bool) : ∀ (c : Clause) (n : ℕ), n ≤ 1 →
    check false n (encodeClause c ++ r) =
      (decide (n+(c.filter fun l => l.2).length ≤ 1) && check false 0 r)
  | [], n, hn => by simp [encodeClause,check,hn]
  | l :: c, n, hn => by
      have he : encodeClause (l :: c) ++ r = encodeLiteral l ++ (encodeClause c ++ r) := by
        simp [encodeClause]
      rw [he,literal]
      cases hb : l.2 with
      | false =>
          simpa [hb] using clause r c n hn
      | true =>
          by_cases h : n < 1
          · simp only [hb,ite_true,h,decide_true,Bool.true_and]
            rw [clause r c (n+1) (by omega)]
            simp only [List.filter_cons,hb,ite_true,List.length_cons]
            have e : n+1+(c.filter fun l => l.2).length = n+((c.filter fun l => l.2).length+1) := by omega
            rw [e]
          · simp only [hb,ite_true,h,decide_false,Bool.false_and,List.filter_cons,List.length_cons]
            have he' : ¬n+((c.filter fun l => l.2).length+1) ≤ 1 := by omega
            rw [decide_eq_false he']
            rfl

private theorem formula (φ : CNF) :
    check false 0 (encodeCNF φ) = true ↔ ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1 := by
  induction φ with
  | nil => simp [encodeCNF,check]
  | cons c φ ih =>
      change check false 0 (encodeClause c ++ encodeCNF φ) = true ↔ _
      rw [clause _ _ _ (by omega)]
      simp [ih]

/-- Canonical Horn-formula syntax has a measured deterministic polynomial-time guard. -/
theorem MeasuredHornGuard :
    {x : List Bool | ∃ φ : CNF, encodeCNF φ = x ∧
      ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1} ∈ P := by
  have hcheck : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => bflag (check false 0 x)) :=
    fst_polyTime _ _ _ trans finish (some (false,0,.b))
      (fun s => (check_run s false 0 (by omega)).symm)
  have hcanon := PEqualNP.Library.SearchHelpers.KSat.Hard.cpt_wfF
  have hm := cpt_comp (g := fun l : List Bool => !l.isEmpty)
    (cpt_sel hcanon (cpt_const []) hcheck) bf_cpt_neL
  have he : (fun x : List Bool => !(sel (bflag (wfB x)) [] (bflag (check false 0 x))).isEmpty) =
      (fun x => wfB x && check false 0 x) := by
    funext s
    cases wfB s <;> cases check false 0 s <;> rfl
  rw [he] at hm
  refine ⟨_,fun x => ?_,hm⟩
  change (∃ φ : CNF, encodeCNF φ = x ∧ ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ↔
    (wfB x && check false 0 x) = true
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨φ,rfl,hφ⟩
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(formula φ).mpr hφ⟩
  · rintro ⟨hw,hc⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff _).mp hw
    exact ⟨φ,rfl,(formula φ).mp hc⟩

end PEqualNP.Outside
