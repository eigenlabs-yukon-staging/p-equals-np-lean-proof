import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Outside.MeasuredClauseMap

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

private abbrev Raw := List Bool

private def words : ℕ → List Literal → CNF
  | 0, _ => [[]]
  | n+1, support => [] :: support.flatMap (fun l => (words n support).map (List.cons l))

private theorem mem_words (support : List Literal) (n : ℕ) (c : Clause) :
    c ∈ words n support ↔ c.length ≤ n ∧ c ⊆ support := by
  induction n generalizing c with
  | zero =>
      constructor
      · intro h
        have he : c = [] := List.mem_singleton.mp h
        subst c
        exact ⟨Nat.zero_le _,by simp⟩
      · rintro ⟨h,_⟩
        exact List.mem_singleton.mpr (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h))
  | succ n ih =>
      constructor
      · intro h
        change c ∈ [] :: support.flatMap _ at h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨Nat.zero_le _,by simp⟩
        · obtain ⟨l,hl,ht⟩ := List.mem_flatMap.mp h
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
          obtain ⟨hlen,hs⟩ := (ih r).mp hr
          exact ⟨Nat.succ_le_succ hlen,fun m hm => (List.mem_cons.mp hm).elim (fun h => h.symm ▸ hl) (fun h => hs h)⟩
      · rintro ⟨hlen,h⟩
        cases c with
        | nil => exact List.mem_cons_self
        | cons l c =>
            apply List.mem_cons_of_mem
            refine List.mem_flatMap.mpr ⟨l,h List.mem_cons_self,
              List.mem_map.mpr ⟨c,?_,rfl⟩⟩
            exact (ih c).mpr ⟨Nat.le_of_succ_le_succ hlen,fun m hm => h (List.mem_cons_of_mem _ hm)⟩

private theorem collect_literals :
    ∃ collect : Raw → Raw, ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) collect ∧
      ∀ φ : CNF, collect (encodeCNF φ) = encodeClause (φ.flatMap id) := by
  obtain ⟨payload,hp,hps⟩ := MeasuredLiteralMap (fun p => p.2) cpt_snd
  obtain ⟨join,hj,hjs⟩ := MeasuredClauseMap payload hp
  let payloads := fun x => join ([],x)
  have ht := cpt_comp (cpt_pair (cpt_const []) cpt_id) hj
  refine ⟨fun x => payloads x ++ [false,false],cpt_app2 ht (cpt_const [false,false]),fun φ => ?_⟩
  simp only [payloads,hjs,hps]
  simp only [encodeClause,List.flatMap_assoc,id_eq]

private theorem words_measured (k : ℕ) :
    ∃ out : Raw → Raw, ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) out ∧
      ∀ lits : Clause, out (encodeClause lits) = encodeCNF (words k lits) := by
  obtain ⟨prepend,hpre,hpres⟩ := MeasuredClauseMap (fun p => p.1 ++ p.2) cpt_append
  let row := fun p : Raw × Raw => prepend (p.2,p.1)
  have hrow : ComputableInPolyTime encodePair (fun x : Raw => x) row :=
    cpt_comp (cpt_pairG cpt_snd cpt_fst) hpre
  obtain ⟨all,ha,has⟩ := MeasuredLiteralMap row hrow
  induction k with
  | zero => exact ⟨fun _ => encodeCNF [[]],cpt_const _,fun _ => rfl⟩
  | succ k ih =>
      obtain ⟨out,ho,hos⟩ := ih
      let scan := fun w => all (out w,w)
      have hscan := cpt_comp (cpt_pair ho cpt_id) ha
      refine ⟨fun w => encodeClause [] ++ scan w,cpt_app2 (cpt_const _) hscan,fun lits => ?_⟩
      simp only [scan,hos,has,row,hpres]
      have he (l : Literal) (c : Clause) : encodeLiteral l ++ encodeClause c = encodeClause (l :: c) := by
        simp [encodeClause]
      simp only [words,encodeCNF,List.flatMap_cons,List.flatMap_assoc,List.flatMap_map,Function.comp_apply,he]

/-- For each fixed width, generate a measured finite universe of canonical
clauses whose literals come from the original formula's signed occurrences. -/
theorem MeasuredBoundedClauseUniverse (k : ℕ) :
    ∃ generate : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) generate ∧
      ∀ φ : CNF, ∃ U : CNF, generate (encodeCNF φ) = encodeCNF U ∧
        ∀ c : Clause, c ∈ U ↔ c.length ≤ k ∧ c ⊆ φ.flatMap id := by
  obtain ⟨source,hs,hss⟩ := collect_literals
  obtain ⟨out,ho,hos⟩ := words_measured k
  refine ⟨fun x => out (source x),cpt_comp hs ho,fun φ => ⟨words k (φ.flatMap id),?_,fun c => mem_words _ _ c⟩⟩
  change out (source (encodeCNF φ)) = _
  rw [hss,hos]

end PEqualNP.Outside
