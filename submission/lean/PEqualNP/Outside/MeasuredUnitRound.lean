import PEqualNP.Outside.UnitPropagationCorrect
import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.TwoSat PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search

private abbrev Raw := List Bool

private def bad (p : Raw × Raw) : Raw :=
  sel (bflag (decide (p.2 = (unpairB p.1).1)))
    (sel (bflag (memB (negI p.2) (unpairB p.1).2)) [true] []) []

private theorem bad_cpt : ComputableInPolyTime encodePair (fun x : Raw => x) bad := by
  have he := cpt_eqF cpt_unpairB2 (cpt_unpairB1_1 cpt_unpairB1)
  have hm := cpt_memB (cpt_negI cpt_unpairB2) (cpt_unpairB2_1 cpt_unpairB1)
  have h : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => bad (unpairB s)) :=
    cpt_sel he (cpt_sel hm (cpt_const [true]) (cpt_const [])) (cpt_const [])
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

private theorem bad_spec (L : List Literal) (l m : Literal) :
    bad (pairB (encodeLiteral l) (L.flatMap encodeLiteral),encodeLiteral m) = [] ↔
    m = l ∨ negLit m ∈ L := by
  have hmem : memB (negI (encodeLiteral m)) (L.flatMap encodeLiteral) = true ↔ negLit m ∈ L := by
    rw [negI_lit]
    exact memB_encL _ _
  have he : encodeLiteral m = encodeLiteral l ↔ m = l :=
    ⟨fun h => encodeLiteral_injective h,congrArg encodeLiteral⟩
  simp only [bad,unpairB_pairB,he]
  by_cases h : m = l
  · simp [h,bflag,sel]
  · simp only [h,decide_false,bflag,sel,ite_true,false_or]
    generalize hv : memB (negI (encodeLiteral m)) (L.flatMap encodeLiteral) = b at hmem ⊢
    cases b <;> simp_all [bflag]

/-- Compute the forceable literal occurrences in a single parallel unit
propagation round. An equality exemption handles repeated copies of the
unit literal as a single member of the corresponding finite-set clause. -/
theorem MeasuredUnitRound :
    ∃ scan : List Bool × List Bool → List Bool,
      ComputableInPolyTime encodePair (fun x : List Bool => x) scan ∧
      ∀ (φ : CNF) (known : List Literal),
        scan (known.flatMap encodeLiteral,encodeCNF φ) =
          (φ.flatMap (fun c => c.filter (fun l =>
            c.all (fun m => decide (m = l) || decide (negLit m ∈ known))))).flatMap encodeLiteral := by
  obtain ⟨check,hcheck,hcs⟩ := MeasuredLiteralMap bad bad_cpt
  let choose := fun z : Raw × Raw =>
    let input := pairB z.2 (unpairB z.1).1
    sel (check (input,(unpairB z.1).2)) z.2 []
  have hc : ComputableInPolyTime encodePair (fun x : Raw => x) choose := by
    have hp := cpt_pairB2 cpt_unpairB2 (cpt_unpairB1_1 cpt_unpairB1)
    have hh := cpt_comp (cpt_pair hp (cpt_unpairB2_1 cpt_unpairB1)) hcheck
    have h : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) (fun s => choose (unpairB s)) :=
      cpt_sel hh cpt_unpairB2 (cpt_const [])
    simpa only [unpairB_pairB] using cpt_comp cpt_pairB h
  obtain ⟨onClause,hoc,hos⟩ := MeasuredLiteralMap choose hc
  let build := fun z : Raw × Raw => onClause (pairB z.1 z.2,z.2)
  have hb : ComputableInPolyTime encodePair (fun x : Raw => x) build :=
    cpt_comp (cpt_pairG cpt_pairB cpt_snd) hoc
  obtain ⟨scan,hs,hss⟩ := MeasuredClauseMap build hb
  refine ⟨scan,hs,fun φ L => ?_⟩
  change scan (L.flatMap encodeLiteral,encodeCNF φ) =
    (φ.flatMap (fun c => c.filter (canForce L c))).flatMap encodeLiteral
  rw [hss,List.flatMap_assoc]
  apply List.flatMap_congr
  intro c _
  simp only [build,hos]
  have hflag (l : Literal) :
      check (pairB (encodeLiteral l) (L.flatMap encodeLiteral),encodeClause c) = [] ↔ canForce L c l = true := by
    rw [hcs,List.flatMap_eq_nil_iff,canForce_spec]
    simp only [bad_spec]
    constructor
    · exact fun h m hm hne => (h m hm).resolve_left hne
    · intro h m hm
      by_cases h' : m = l
      · exact Or.inl h'
      · exact Or.inr (h m hm h')
  have he (l : Literal) :
      choose (pairB (L.flatMap encodeLiteral) (encodeClause c),encodeLiteral l) =
        if canForce L c l then encodeLiteral l else [] := by
    simp only [choose,unpairB_pairB,sel]
    rw [if_congr (hflag l) rfl rfl]
  simp only [he]
  induction c with
  | nil => rfl
  | cons l c ih =>
      have h (p : Literal → Bool) (xs : Clause) :
          xs.flatMap (fun l => if p l then encodeLiteral l else []) =
          (xs.filter p).flatMap encodeLiteral := by
        induction xs with
        | nil => rfl
        | cons a as h =>
            cases ha : p a <;> simp [ha,h]
      exact h _ _

private def notFalsifiedLit (p : Raw × Raw) : Raw :=
  sel (bflag (memB (negI p.2) p.1)) [true] []

private theorem notFalsifiedLit_cpt : ComputableInPolyTime encodePair (fun x : Raw => x) notFalsifiedLit := by
  have h : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x)
      (fun r => notFalsifiedLit (unpairB r)) :=
    cpt_sel (cpt_memB (cpt_negI cpt_unpairB2) cpt_unpairB1) (cpt_const [true]) (cpt_const [])
  simpa only [unpairB_pairB] using cpt_comp cpt_pairB h

/-- Test whether at least one clause is fully falsified by the supplied list
of known true literals. Empty clauses satisfy the all-literals condition. -/
theorem MeasuredCNFFalsified :
    ∃ test : List Bool × List Bool → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool test ∧
      ∀ (φ : CNF) (known : List Literal),
        test (known.flatMap encodeLiteral,encodeCNF φ) = true ↔
          ∃ c ∈ φ, ∀ l ∈ c, negLit l ∈ known := by
  obtain ⟨unforced,hu,hus⟩ := MeasuredLiteralMap notFalsifiedLit notFalsifiedLit_cpt
  let check := fun z : Raw × Raw => sel (unforced z) [true] []
  have hc : ComputableInPolyTime encodePair (fun x : Raw => x) check := by
    have h := cpt_sel (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hu)
      (cpt_const [true]) (cpt_const [])
    simpa [check,unpairB_pairB] using cpt_comp cpt_pairB h
  obtain ⟨all,ha,hs⟩ := MeasuredClauseMap check hc
  refine ⟨fun p => !(all p).isEmpty,cpt_comp (g := fun w : Raw => !w.isEmpty) ha bf_cpt_neL,
    fun φ L => ?_⟩
  have hcheck (c : Clause) :
      check (L.flatMap encodeLiteral,encodeClause c) ≠ [] ↔ ∀ l ∈ c, negLit l ∈ L := by
    have hsel : check (L.flatMap encodeLiteral,encodeClause c) ≠ [] ↔
        unforced (L.flatMap encodeLiteral,encodeClause c) = [] := by
      unfold check
      cases unforced (L.flatMap encodeLiteral,encodeClause c) <;> simp [sel]
    rw [hsel,hus,List.flatMap_eq_nil_iff]
    apply forall_congr'
    intro l
    apply imp_congr_right
    intro _
    have h : memB (negI (encodeLiteral l)) (L.flatMap encodeLiteral) = true ↔ negLit l ∈ L := by
      rw [negI_lit]
      exact memB_encL _ _
    rw [← h]
    unfold notFalsifiedLit
    cases memB (negI (encodeLiteral l)) (L.flatMap encodeLiteral) <;> simp [bflag,sel]
  simp only [Bool.not_eq_true',List.isEmpty_eq_false_iff,hs,ne_eq,List.flatMap_eq_nil_iff]
  classical
  push_neg
  exact exists_congr (fun c => and_congr_right (fun _ => hcheck c))

end PEqualNP.Outside
