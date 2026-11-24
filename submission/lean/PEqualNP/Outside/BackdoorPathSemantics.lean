import PEqualNP.Outside.BackdoorPathMachine
import PEqualNP.Outside.BackdoorBranch
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside.BackdoorPathSemantics

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.BackdoorPathMachine
open PEqualNP.Outside.TripleObstructionSemantics (Triple encodeTriple firstBad obstruction_enc firstBad_none)
open PEqualNP.Outside.BackdoorBranch
open PEqualNP.Outside.CnfRestrictionSemantics (names valueOf run_enc)
open PEqualNP.Outside.RestrictCnfHelpers

def branchIndex (bits : Word) : Fin 3 :=
  if bits.headD false then if bits.tail.headD false then 2 else 1 else 0

def branchBits (j : Fin 3) (b : Bool) : Word :=
  [decide (j.val ≠ 0), decide (j.val = 2), b]

theorem branch_index (j : Fin 3) (b : Bool) (tail : Word) :
    branchIndex (branchBits j b ++ tail) = j := by
  fin_cases j <;> rfl

theorem branch_value (j : Fin 3) (b : Bool) (tail : Word) :
    (branchBits j b ++ tail).tail.tail.headD false = b := by
  rfl

theorem branch_tail (j : Fin 3) (b : Bool) (tail : Word) :
    (branchBits j b ++ tail).tail.tail.tail = tail := by
  rfl

theorem pick_enc (t : Triple) (b : Word) :
    pick (encodeTriple t) b = vcode (selectedName t (branchIndex b)) := by
  rcases b with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [pick, branchIndex, encodeTriple, unpairB_pairB, bflag, sel, selectedName]
  · cases a <;> simp [pick, branchIndex, encodeTriple, unpairB_pairB, bflag, sel, selectedName]
  · cases a <;> cases c <;>
      simp [pick, branchIndex, encodeTriple, unpairB_pairB, bflag, sel, selectedName]

theorem step_done (φ : CNF) (k v : List ℕ) (b : Word) (h : firstBad k φ = none) :
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names k) (names v) b := by
  simp [step, pack, formula, selected, setTrue, BackdoorPathMachine.code, unpairB_pairB, obstruction_enc, h, sel]

theorem step_next (φ : CNF) (k v : List ℕ) (b : Word) (t : Triple)
    (h : firstBad k φ = some t) :
    let i := selectedName t (branchIndex b)
    step (pack (encodeCNF φ) (names k) (names v) b) =
      pack (encodeCNF φ) (names (k ++ [i]))
        (names (v ++ if b.tail.tail.headD false then [i] else [])) b.tail.tail.tail := by
  simp only [step, pack, formula, selected, setTrue, BackdoorPathMachine.code, unpairB_pairB, obstruction_enc, h,
    Option.map_some, Option.getD_some]
  have hn : encodeTriple t ≠ [] := by simp [encodeTriple, pairB]
  have hlen := (triple_member h (branchIndex b)).2
  rw [pick_enc, cut_eq, List.take_of_length_le hlen]
  cases hbit : b.tail.tail.head?.getD false <;> simp at hbit <;>
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

theorem query_sound (φ : CNF) (b : Word)
    (h : query (encodeCNF φ, b) ∈ KSAT 2) : Satisfiable φ := by
  obtain ⟨k, v, b', he⟩ := iter_valid φ [] [] b b.length
  have he' : query (encodeCNF φ, b) = encodeCNF (restrict (valueOf k v) φ) := by
    change finish (step^[b.length] (pack (encodeCNF φ) [] [] b)) = _
    change step^[b.length] (pack (encodeCNF φ) [] [] b) = _ at he
    rw [he, finish_enc]
  obtain ⟨ψ, _, hc, hs⟩ := h
  rw [he'] at hc
  have eq := PEqualNP.Library.SearchHelpers.encodeCNF_injective hc
  rw [eq] at hs
  obtain ⟨σ, hσ, _⟩ := (sat_restrict_iff _ _).mp hs
  exact ⟨σ, hσ⟩

end PEqualNP.Outside.BackdoorPathSemantics
