import PEqualNP.Outside.UniqueNameScan
import PEqualNP.Outside.CnfRestrictionMachine
import PEqualNP.Outside.CnfRestrictionSemantics

namespace PEqualNP.Outside.AllFormulaNames

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.CnfRestrictionMachine (cpt_isEndF)
open PEqualNP.Outside.CnfRestrictionSemantics (names)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def step (z : Word) : Word :=
  let r := (unpairB z).1
  let a := (unpairB z).2
  sel r z (pairB (dropI r) (sel (bflag (isEnd r)) (a ++ (headI r).tail.tail) a))

theorem step_cpt : CPT step := by
  have hr := cpt_unpairB1
  have ha := cpt_unpairB2
  have hn := cpt_tail1 (cpt_tail1 (cpt_comp hr cpt_headI))
  have hf := cpt_sel (cpt_comp hr cpt_isEndF) (cpt_app2 ha hn) ha
  exact cptl (cpt_sel hr cpt_id (cpt_pairB2 (cpt_comp hr cpt_dropI) hf)) (fun _ => rfl)

theorem step_length (z : Word) : (step z).length ≤ z.length + 1 := by
  have h := unpairB_length z
  have hdrop := dropI_length (unpairB z).1
  have hhead := congrArg List.length (headI_dropI (unpairB z).1)
  simp only [List.length_append] at hhead
  simp only [step, sel]
  split
  · omega
  · simp only [pairB_length]
    split
    · simp only [List.length_append, List.length_tail]
      omega
    · omega

def gather (w : Word) : Word := (unpairB (step^[w.length] (pairB w []))).2

theorem gather_cpt : CPT gather := by
  obtain ⟨m⟩ := step_cpt
  have loop := Iter.iter_polyTime step m 1 step_length
  have h := cpt_comp (cpt_comp (cpt_pair (cpt_pairB2 cpt_id (cpt_const [])) cpt_id) loop) cpt_unpairB2
  exact h

def vars (φ : CNF) : List ℕ := φ.flatMap (fun c => c.map Prod.fst)

def distinct (φ : CNF) : List ℕ := UniqueNameScan.scan [] (vars φ)

theorem step_lit (l : Literal) (r a : Word) :
    step (pairB (encodeLiteral l ++ r) a) = pairB r (a ++ vcode l.1) := by
  have hn : encodeLiteral l ++ r ≠ [] := by simp [encodeLiteral_eq]
  simp only [step, unpairB_pairB, sel, hn, isEnd_lit, bflag, Bool.false_eq_true, ite_false,
    dropI_lit, headI_lit]
  simp [encodeLiteral_eq]

theorem step_close (r a : Word) :
    step (pairB ([false, false] ++ r) a) = pairB r a := by
  simp [step, unpairB_pairB, sel, isEnd, bflag, dropI]

theorem scan_clause (c : Clause) (r a : Word) :
    step^[c.length] (pairB (c.flatMap encodeLiteral ++ r) a) =
      pairB r (a ++ names (c.map Prod.fst)) := by
  induction c generalizing a with
  | nil => simp [names]
  | cons l c ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, step_lit, ih, names, List.map_cons]

theorem scan (φ : CNF) (a : Word) :
    step^[nIt φ] (pairB (encodeCNF φ) a) = pairB [] (a ++ names (vars φ)) := by
  induction φ generalizing a with
  | nil => simp [nIt, vars, names, encodeCNF]
  | cons c cs ih =>
    have hn : nIt (c :: cs) = nIt cs + (c.length + 1) := by simp [nIt, Nat.add_comm]
    have he : encodeCNF (c :: cs) = c.flatMap encodeLiteral ++ ([false, false] ++ encodeCNF cs) := by
      simp [encodeCNF, encodeClause, List.append_assoc]
    rw [hn, he, Function.iterate_add_apply, Function.iterate_succ_apply', scan_clause, step_close, ih]
    simp [vars, names, List.flatMap_append, List.append_assoc]

theorem gather_enc (φ : CNF) : gather (encodeCNF φ) = names (vars φ) := by
  have hn := nIt_le φ
  have he := scan φ []
  have hfix : step (pairB [] (names (vars φ))) = pairB [] (names (vars φ)) := by
    simp [step, sel, unpairB_pairB]
  unfold gather
  simp only [List.nil_append] at he
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, he, Function.iterate_fixed hfix, unpairB_pairB]

def collect (w : Word) : Word := UniqueNameScan.unique (gather w)

theorem collect_cpt : CPT collect := by
  have h := cpt_comp gather_cpt UniqueNameScan.unique_cpt
  exact h

theorem collect_enc (φ : CNF) : collect (encodeCNF φ) = names (distinct φ) := by
  unfold collect
  rw [gather_enc]
  exact UniqueNameScan.unique_enc (vars φ)

theorem mem_distinct (φ : CNF) (i : ℕ) :
    i ∈ distinct φ ↔ ∃ c ∈ φ, ∃ l ∈ c, l.1 = i := by
  simp [distinct, UniqueNameScan.mem_scan, vars, List.mem_flatMap, List.mem_map]

theorem distinct_length (φ : CNF) : (distinct φ).length ≤ (encodeCNF φ).length := by
  calc
    _ = (vars φ).toFinset.card := UniqueNameScan.scan_count (vars φ)
    _ ≤ (vars φ).length := List.toFinset_card_le (vars φ)
    _ ≤ nIt φ := by
      induction φ with
      | nil => simp [nIt, vars]
      | cons c cs ih =>
        simp only [vars, List.flatMap_cons, List.length_append, List.length_map, nIt] at *
        omega
    _ ≤ _ := nIt_le φ

end PEqualNP.Outside.AllFormulaNames
