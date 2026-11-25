import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search

private abbrev Raw := List Bool

private def move (s : Raw) : Raw :=
  let rem := (unpairB s).1
  let out := (unpairB s).2
  sel (hd rem) s (pairB (dropI rem) (headI rem ++ out))

private theorem move_cpt : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) move :=
  cpt_sel (cpt_comp cpt_unpairB1 cpt_hd) cpt_id
    (cpt_pairB2 (cpt_comp cpt_unpairB1 cpt_dropI)
      (cpt_app2 (cpt_comp cpt_unpairB1 cpt_headI) cpt_unpairB2))

private theorem move_bound (s : Raw) : (move s).length ≤ s.length + 1 := by
  dsimp only [move,sel]
  split
  · omega
  · have hp := unpairB_length s
    have hl := congrArg List.length (headI_dropI (unpairB s).1)
    simp only [List.length_append] at hl
    simp only [pairB_length,List.length_append]
    omega

private theorem encoded_cons (l : Literal) (c : Clause) :
    encodeClause (l::c) = encodeLiteral l ++ encodeClause c := by
  simp [encodeClause]

private theorem move_lit (l : Literal) (c d : Clause) :
    move (pairB (encodeClause (l::c)) (encodeClause d)) =
      pairB (encodeClause c) (encodeClause (l::d)) := by
  have h : hd (encodeLiteral l ++ encodeClause c) ≠ [] := by
    simp [hd,encodeLiteral_eq]
  simp only [move,unpairB_pairB,encoded_cons,sel,h,ite_false,dropI_lit,headI_lit]

private theorem move_done (d : Clause) :
    move (pairB (encodeClause []) (encodeClause d)) = pairB (encodeClause []) (encodeClause d) := by
  simp only [move,unpairB_pairB,show hd (encodeClause []) = [] by rfl,sel,ite_true]

private theorem walk (c d : Clause) (n : ℕ) (hn : c.length ≤ n) :
    move^[n] (pairB (encodeClause c) (encodeClause d)) =
      pairB (encodeClause []) (encodeClause (c.reverse ++ d)) := by
  induction c generalizing n d with
  | nil =>
    clear hn
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply,move_done,ih]
  | cons l c ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [Function.iterate_succ_apply,move_lit,ih _ n (by simpa using hn)]
      simp [List.reverse_cons,List.append_assoc]

/-- Reverse the sequence of literal words in a canonical clause, retaining
the bit order inside each literal and the final clause delimiter. -/
theorem MeasuredReverseClause :
    ∃ reverse : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) reverse ∧
      ∀ c : Clause, reverse (encodeClause c) = encodeClause c.reverse := by
  let run := fun s : Raw => (unpairB (move^[s.length] (pairB s (encodeClause [])))).2
  have hi := cpt_pairB2 cpt_id (cpt_const (encodeClause []))
  have hr := cpt_unpairB2_1 (cpt_iterGrow move_cpt 1 move_bound cpt_id hi)
  refine ⟨run,hr,fun c => ?_⟩
  have hlen : c.length ≤ (encodeClause c).length := by
    induction c with
    | nil => simp
    | cons l c ih =>
      rw [List.length_cons,encoded_cons,List.length_append]
      have h : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega
  simp only [run,walk c [] _ hlen,unpairB_pairB,List.append_nil]

end PEqualNP.Outside
