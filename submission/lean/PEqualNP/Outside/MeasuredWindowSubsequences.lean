import PEqualNP.Outside.MeasuredClauseMap
import Mathlib.Data.List.Sublists

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Search

private abbrev Raw := List Bool

private def subsequences : Clause → CNF
  | [] => [[]]
  | l::c => subsequences c ++ (subsequences c).map (List.cons l)

private theorem subseq_correct (c d : Clause) :
    d ∈ subsequences c ↔ d.Sublist c := by
  induction c generalizing d with
  | nil => simp [subsequences]
  | cons l c ih =>
    simp only [subsequences,List.mem_append,List.mem_map,ih]
    constructor
    · rintro (h | ⟨u,hu,rfl⟩)
      · exact List.Sublist.cons _ h
      · exact List.Sublist.cons₂ _ hu
    · intro h
      cases h with
      | cons _ h => exact Or.inl h
      | cons_cons _ h => exact Or.inr ⟨_,h,rfl⟩

private theorem subseq_length (c : Clause) : (subsequences c).length = 2 ^ c.length := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [subsequences,List.length_append,List.length_map,List.length_cons,ih,pow_succ]
    omega

private theorem measured (m : ℕ) :
    ∃ gen : Raw → Raw, ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) gen ∧
      ∀ c : Clause, gen (encodeClause c) = encodeCNF (subsequences (c.take m)) := by
  obtain ⟨prepend,hp,hps⟩ := MeasuredClauseMap (fun p => p.1 ++ p.2) cpt_append
  induction m with
  | zero => exact ⟨fun _ => encodeCNF [[]],cpt_const _,fun _ => rfl⟩
  | succ m ih =>
    obtain ⟨gen,hg,hgs⟩ := ih
    let tail := fun s : Raw => gen (dropI s)
    let extended := fun s : Raw => prepend (headI s,tail s)
    let run := fun s : Raw => sel (hd s) (encodeCNF [[]]) (tail s ++ extended s)
    have ht : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) tail := cpt_comp cpt_dropI hg
    have he : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) extended :=
      cpt_comp (cpt_pair cpt_headI ht) hp
    refine ⟨run,cpt_sel cpt_hd (cpt_const _) (cpt_app2 ht he),fun c => ?_⟩
    cases c with
    | nil => rfl
    | cons l c =>
      have hcode : encodeClause (l::c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      have hhead : hd (encodeLiteral l ++ encodeClause c) ≠ [] := by simp [hd,encodeLiteral_eq]
      simp only [run,hcode,sel,hhead,ite_false,tail,extended,dropI_lit,headI_lit,hgs,hps]
      have happ (u : Clause) : encodeLiteral l ++ encodeClause u = encodeClause (l::u) := by simp [encodeClause]
      simp only [List.take_succ_cons,subsequences,encodeCNF,List.flatMap_append,List.flatMap_map,
        Function.comp_apply,happ]

/-- Enumerate, from a fixed-length prefix, all position subsequences as
canonical clauses. The number of generated rows is exactly a power of two. -/
theorem MeasuredWindowSubsequences (m : ℕ) :
    ∃ gen : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen ∧
      ∀ c : Clause, ∃ U : CNF, gen (encodeClause c) = encodeCNF U ∧
        U.length = 2 ^ (min m c.length) ∧
        ∀ d : Clause, d ∈ U ↔ d.Sublist (c.take m) := by
  obtain ⟨gen,hg,hgs⟩ := measured m
  refine ⟨gen,hg,fun c => ⟨subsequences (c.take m),hgs c,?_,fun d => subseq_correct _ d⟩⟩
  simp [subseq_length]

end PEqualNP.Outside
