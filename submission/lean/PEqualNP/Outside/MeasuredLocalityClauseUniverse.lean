import PEqualNP.Outside.MeasuredLiteralSuffixMap
import PEqualNP.Outside.MeasuredSignedLiteralWindow
import PEqualNP.Outside.MeasuredWindowSubsequences

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private abbrev Raw := List Bool

private def signedWindow (k : ℕ) (c : Clause) :=
  (c.take (k+1)).flatMap (fun l => [l,(l.1,!l.2)])

private theorem signed_bound (k : ℕ) (c : Clause) : (signedWindow k c).length ≤ 2*(k+1) := by
  have h (s : Clause) : (s.flatMap (fun l => [l,(l.1,!l.2)])).length = 2*s.length := by
    induction s with
    | nil => rfl
    | cons l s ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]
      omega
  simp only [signedWindow,h,List.length_take]
  exact Nat.mul_le_mul_left _ (Nat.min_le_left _ _)

private theorem flat_bound {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) :
    (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Generate all subclauses of signed consecutive windows. The number
of emitted clauses is linear in the literal count for a fixed radius. -/
theorem MeasuredLocalityClauseUniverse (k : ℕ) :
    let window := fun (c : Clause) (i : ℕ) =>
      ((c.drop i).take (k+1)).flatMap (fun l => [l,(l.1,!l.2)])
    ∃ gen : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen ∧
      ∀ c : Clause, ∃ U : CNF, gen (encodeClause c) = encodeCNF U ∧
        U.length ≤ 1 + c.length * 2^(2*(k+1)) ∧
        ∀ d : Clause, d ∈ U ↔ d = [] ∨ ∃ i < c.length, d.Sublist (window c i) := by
  dsimp only
  classical
  obtain ⟨make,hm,hms⟩ := MeasuredSignedLiteralWindow (k+1)
  obtain ⟨gen,hg,hgs⟩ := MeasuredWindowSubsequences (2*(k+1))
  choose rows hRows hLength hMem using hgs
  let scanOne := fun p : Raw × Raw => gen (make p.2)
  have hOne : ComputableInPolyTime encodePair (fun x : Raw => x) scanOne :=
    cpt_comp (g := fun s : Raw => gen (make s)) cpt_snd (cpt_comp (g := gen) hm hg)
  obtain ⟨scan,hs,hss⟩ := MeasuredLiteralSuffixMap scanOne hOne
  let run := fun s : Raw => encodeClause [] ++ scan ([],s)
  have hRun : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) run :=
    cpt_app2 (cpt_const _) (cpt_comp (cpt_pair (cpt_const []) cpt_id) hs)
  refine ⟨run,hRun,fun c => ?_⟩
  let atSuffix := fun i => rows (signedWindow k (c.drop i))
  let U := [] :: (List.range c.length).flatMap atSuffix
  have hOneCode (d : Clause) : scanOne ([],encodeClause d) = encodeCNF (rows (signedWindow k d)) := by
    simp only [scanOne,hms,signedWindow,hRows]
  have hSize (d : Clause) : (rows (signedWindow k d)).length ≤ 2^(2*(k+1)) := by
    rw [hLength,Nat.min_eq_right (signed_bound k d)]
    exact Nat.pow_le_pow_right (by decide) (signed_bound k d)
  have hFits (c d : Clause) : d ∈ rows (signedWindow k c) ↔ d.Sublist (signedWindow k c) := by
    rw [hMem,List.take_of_length_le (signed_bound k c)]
  refine ⟨U,?_,?_,fun d => ?_⟩
  · change encodeClause [] ++ scan ([],encodeClause c) = _
    rw [hss]
    simp only [hOneCode,U,atSuffix,encodeCNF,List.flatMap_cons,List.flatMap_assoc]
  · have h := flat_bound (List.range c.length) atSuffix (2^(2*(k+1))) (fun i _ => hSize (c.drop i))
    simpa [U,List.length_range,Nat.add_comm] using Nat.succ_le_succ h
  · change d ∈ U ↔ d = [] ∨ ∃ i < c.length, d.Sublist (signedWindow k (c.drop i))
    simp only [U,List.mem_cons,List.mem_flatMap,List.mem_range,atSuffix,hFits]

end PEqualNP.Outside
