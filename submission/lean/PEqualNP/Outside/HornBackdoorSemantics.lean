import PEqualNP.Outside.HornBackdoorCore
import PEqualNP.Outside.HornBackdoorBranch
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside.HornBackdoorSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathCore (Word pack formula selected setTrue code cut_eq finish)
open PEqualNP.Outside.BackdoorChunkCore (advanceChunk)
open PEqualNP.Outside.HornBackdoorCore
open PEqualNP.Outside.PositivePairSemantics (NamePair encodeNames firstBad obstruction_enc firstBad_none)
open PEqualNP.Outside.HornBackdoorBranch
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers

def branchBits (j b : Bool) : Word := [j, b]

theorem branch_index (j b : Bool) (tail : Word) :
    (branchBits j b ++ tail).headD false = j := rfl

theorem branch_value (j b : Bool) (tail : Word) :
    ((branchBits j b ++ tail).drop 1).headD false = b := rfl

theorem branch_tail (j b : Bool) (tail : Word) :
    (branchBits j b ++ tail).drop 2 = tail := rfl

theorem pick_enc (t : NamePair) (b : Word) :
    pick (encodeNames t) b = vcode (selectedName t (b.headD false)) := by
  rcases b with _ | ⟨a, tail⟩
  · simp [pick, encodeNames, unpairB_pairB, bflag, sel, selectedName]
  · cases a <;> simp [pick, encodeNames, unpairB_pairB, bflag, sel, selectedName]

theorem step_done (φ : CNF) (k v : List ℕ) (b : Word) (h : firstBad k φ = none) :
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names k) (names v) b := by
  simp [step, advanceChunk, probe, pack, formula, selected, unpairB_pairB, obstruction_enc, h, sel]

theorem step_next (φ : CNF) (k v : List ℕ) (b : Word) (t : NamePair)
    (h : firstBad k φ = some t) :
    let i := selectedName t (b.headD false)
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names (k ++ [i]))
        (names (v ++ if (b.drop 1).headD false then [i] else [])) (b.drop 2) := by
  have hn : encodeNames t ≠ [] := by simp [encodeNames, pairB]
  have hlen := (pair_member h (b.headD false)).2
  simp only [step, advanceChunk, choose, probe, pack, formula, selected, setTrue,
    BackdoorPathCore.code, unpairB_pairB, obstruction_enc, h, Option.map_some, Option.getD_some]
  rw [pick_enc, cut_eq, List.take_of_length_le hlen]
  cases hbit : b[1]?.getD false <;>
    simp [sel, hn, bflag, hbit, names, List.flatMap_append]

theorem iter_valid (φ : CNF) (k v : List ℕ) (b : Word) (n : ℕ) :
    ∃ k' v' : List ℕ, ∃ b' : Word,
      step^[n] (pack (encodeCNF φ) (names k) (names v) b) =
        pack (encodeCNF φ) (names k') (names v') b' := by
  induction n generalizing k v b with
  | zero => exact ⟨k, v, b, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases h : firstBad k φ with
    | none =>
      rw [step_done φ k v b h]
      exact ih k v b
    | some t =>
      rw [step_next φ k v b t h]
      exact ih _ _ _

theorem finish_enc (φ : CNF) (k v : List ℕ) (b : Word) :
    finish (pack (encodeCNF φ) (names k) (names v) b) =
      encodeCNF (restrict (valueOf k v) φ) := by
  simp only [finish, pack, formula, selected, setTrue, unpairB_pairB, run_enc]

theorem query_sound (L : Language Bool)
    (sound : ∀ x, x ∈ L → x ∈ SAT) (φ : CNF) (b : Word)
    (h : query (encodeCNF φ, b) ∈ L) : Satisfiable φ := by
  obtain ⟨k, v, b', he⟩ := iter_valid φ [] [] b b.length
  have he' : query (encodeCNF φ, b) = encodeCNF (restrict (valueOf k v) φ) := by
    change finish (step^[b.length] (pack (encodeCNF φ) [] [] b)) = _
    change step^[b.length] (pack (encodeCNF φ) [] [] b) = _ at he
    rw [he, finish_enc]
  obtain ⟨ψ, hc, hs⟩ := sound _ h
  rw [he'] at hc
  have eq := PEqualNP.Library.SearchHelpers.encodeCNF_injective hc
  rw [eq] at hs
  obtain ⟨σ, hσ, _⟩ := (sat_restrict_iff _ _).mp hs
  exact ⟨σ, hσ⟩

end PEqualNP.Outside.HornBackdoorSemantics
