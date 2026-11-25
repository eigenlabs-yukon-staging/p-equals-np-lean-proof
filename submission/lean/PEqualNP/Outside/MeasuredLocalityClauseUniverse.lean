import PEqualNP.Outside.MeasuredLiteralSuffixMap
import PEqualNP.Outside.MeasuredSignedLiteralWindow
import PEqualNP.Outside.MeasuredWindowSubsequences
import PEqualNP.Outside.WindowWeightBound
import Mathlib.Tactic.Ring

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

private def weight (c : Clause) : ℕ := (c.map (fun l => (encodeLiteral l).length)).sum

private theorem clause_weight (c : Clause) : (encodeClause c).length = weight c + 2 := by
  simp [encodeClause,weight,List.length_flatMap]

private theorem signed_weight (c : Clause) :
    weight (c.flatMap (fun l => [l,(l.1,!l.2)])) = 2 * weight c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have he : (encodeLiteral (l.1,!l.2)).length = (encodeLiteral l).length := by simp [encodeLiteral]
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,weight,List.map_cons,List.sum_cons] at ih ⊢
    omega

private theorem mono_sum {α : Type} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    exact Nat.add_le_add (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem sum_mul_add {α : Type} (l : List α) (f : α → ℕ) (A B C : ℕ) :
    (l.map (fun i => A*(B*f i+C))).sum = A*(B*(l.map f).sum+C*l.length) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
    ring

private theorem catalogue_bit_bound (k : ℕ) (c : Clause) (rows : ℕ → CNF)
    (hSize : ∀ i < c.length, (rows i).length ≤ 2^(2*(k+1)))
    (hSub : ∀ i < c.length, ∀ d ∈ rows i, d.Sublist (signedWindow k (c.drop i))) :
    (encodeCNF ([] :: (List.range c.length).flatMap rows)).length ≤
      2+2^(2*(k+1))*(2*(k+2)*(encodeClause c).length) := by
  let inds := List.range c.length
  let M := 2^(2*(k+1))
  let localWeight := fun i => weight ((c.drop i).take (k+1))
  have hLen (i : ℕ) (hi : i ∈ inds) :
      (encodeCNF (rows i)).length ≤ M*(2*localWeight i+2) := by
    have hlt := List.mem_range.mp hi
    have hWindow := calc
      (encodeClause (signedWindow k (c.drop i))).length =
          weight (signedWindow k (c.drop i))+2 := clause_weight _
      _ = 2*localWeight i+2 := by rw [signedWindow,signed_weight]
    have hb : ∀ d ∈ rows i, (encodeClause d).length ≤ 2*localWeight i+2 := by
      intro d hd
      rw [← hWindow]
      have h := ((hSub i hlt d hd).flatMap encodeLiteral).length_le
      simp only [encodeClause,List.length_append,List.length_cons,List.length_nil]
      exact Nat.add_le_add_right h _
    exact (flat_bound (rows i) encodeClause _ hb).trans (Nat.mul_le_mul_right _ (hSize i hlt))
  have hSum : (inds.map localWeight).sum ≤ (k+1)*weight c := by
    simpa only [inds,localWeight,weight,List.length_map,List.map_drop,List.map_take] using
      WindowWeightBound (k+1) (c.map (fun l => (encodeLiteral l).length))
  have hC : c.length ≤ weight c := by
    have h := PEqualNP.Library.SearchHelpers.SatV.length_le_flatMap_lit c
    simpa only [weight,List.length_flatMap] using h
  have hFormula :
      (encodeCNF ([] :: inds.flatMap rows)).length =
        2+(inds.map (fun i => (encodeCNF (rows i)).length)).sum := by
    have h0 : (encodeClause []).length = 2 := rfl
    simp only [encodeCNF,List.flatMap_cons,List.length_append,h0,List.flatMap_assoc]
    rw [List.length_flatMap]
  rw [hFormula]
  apply Nat.add_le_add_left
  calc
    _ ≤ (inds.map (fun i => M*(2*localWeight i+2))).sum :=
      mono_sum inds _ _ hLen
    _ = M*(2*(inds.map localWeight).sum+2*inds.length) := sum_mul_add inds _ M 2 2
    _ ≤ M*(2*((k+1)*weight c)+2*c.length) := by
      apply Nat.mul_le_mul_left
      rw [show inds.length = c.length by simp [inds]]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hSum) (Nat.le_refl _)
    _ ≤ M*(2*((k+1)*weight c)+2*weight c) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hC) _)
    _ = M*(2*(k+2)*weight c) := by ring
    _ ≤ M*(2*(k+2)*(encodeClause c).length) := by
      rw [clause_weight]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

/-- Generate all subclauses of signed consecutive windows. The number
of emitted clauses is linear in the literal count for a fixed radius. -/
theorem measuredLocalityClauseUniverse_bounded (k : ℕ) :
    let window := fun (c : Clause) (i : ℕ) =>
      ((c.drop i).take (k+1)).flatMap (fun l => [l,(l.1,!l.2)])
    ∃ gen : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen ∧
      ∀ c : Clause, ∃ U : CNF, gen (encodeClause c) = encodeCNF U ∧
        U.length ≤ 1 + c.length * 2^(2*(k+1)) ∧
        (encodeCNF U).length ≤ 2+2^(2*(k+1))*(2*(k+2)*(encodeClause c).length) ∧
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
  refine ⟨U,?_,?_,?_,fun d => ?_⟩
  · change encodeClause [] ++ scan ([],encodeClause c) = _
    rw [hss]
    simp only [hOneCode,U,atSuffix,encodeCNF,List.flatMap_cons,List.flatMap_assoc]
  · have h := flat_bound (List.range c.length) atSuffix (2^(2*(k+1))) (fun i _ => hSize (c.drop i))
    simpa [U,List.length_range,Nat.add_comm] using Nat.succ_le_succ h
  · exact catalogue_bit_bound k c atSuffix (fun i _ => hSize (c.drop i))
      (fun i _ d hm => (hFits (c.drop i) d).mp hm)
  · change d ∈ U ↔ d = [] ∨ ∃ i < c.length, d.Sublist (signedWindow k (c.drop i))
    simp only [U,List.mem_cons,List.mem_flatMap,List.mem_range,atSuffix,hFits]

/-- Generate all signed contiguous-window subclauses and bound the
number of generated canonical rows. -/
theorem MeasuredLocalityClauseUniverse (k : ℕ) :
    let window := fun (c : Clause) (i : ℕ) =>
      ((c.drop i).take (k+1)).flatMap (fun l => [l,(l.1,!l.2)])
    ∃ gen : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen ∧
      ∀ c : Clause, ∃ U : CNF, gen (encodeClause c) = encodeCNF U ∧
        U.length ≤ 1 + c.length * 2^(2*(k+1)) ∧
        ∀ d : Clause, d ∈ U ↔ d = [] ∨ ∃ i < c.length, d.Sublist (window c i) := by
  obtain ⟨gen,hg,hgs⟩ := measuredLocalityClauseUniverse_bounded k
  refine ⟨gen,hg,fun c => ?_⟩
  obtain ⟨U,hU,hSize,_,hRows⟩ := hgs c
  exact ⟨U,hU,hSize,hRows⟩

end PEqualNP.Outside
