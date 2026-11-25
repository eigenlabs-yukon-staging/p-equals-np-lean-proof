import PEqualNP.Outside.MeasuredLiteralMap
import PEqualNP.Outside.MeasuredClauseMap
import PEqualNP.Outside.MeasuredFirstClause
import PEqualNP.Library.SearchHelpers.KSatHard

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

def hornPairs (φ : CNF) : CNF :=
  φ.filterMap fun c => match c.filter (fun l => l.2) with
    | l :: m :: _ => some [(l.1,true),(m.1,true)]
    | _ => none

def hornKeys (φ : CNF) : List ℕ := ((hornPairs φ).headD []).map Prod.fst

private theorem pairs_spec (φ : CNF) (p : Clause) :
    p ∈ hornPairs φ ↔
      ∃ c ∈ φ, ∃ l m r, c.filter (fun l => l.2) = l :: m :: r ∧ p = [(l.1,true),(m.1,true)] := by
  rw [hornPairs,List.mem_filterMap]
  constructor
  · rintro ⟨c,hc,h⟩
    generalize he : (List.filter (fun l => l.2) c) = d at h
    cases d with
    | nil => contradiction
    | cons l ds =>
        cases ds with
        | nil => contradiction
        | cons m r =>
            obtain rfl : [(l.1,true),(m.1,true)] = p := Option.some.inj h
            exact ⟨c,hc,l,m,r,he,rfl⟩
  · rintro ⟨c,hc,l,m,r,he,rfl⟩
    exact ⟨c,hc,by rw [he]⟩

theorem hornKeys_characterize (φ : CNF) :
    (hornKeys φ = [] ↔ ∀ c ∈ φ, (c.filter fun l => l.2).length ≤ 1) ∧
    ((hornKeys φ).length ≤ 2) ∧
    ∀ xs : List ℕ, (∀ c ∈ φ, (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1) →
      hornKeys φ ≠ [] → ∃ x ∈ hornKeys φ, x ∈ xs := by
  cases he : hornPairs φ with
  | nil =>
      have hk : hornKeys φ = [] := by simp [hornKeys,he]
      simp only [hk,true_iff,List.length_nil,Nat.zero_le,true_and,ne_eq,not_true_eq_false,false_implies,implies_true,and_true]
      intro c hc
      by_contra h
      generalize hp : (List.filter (fun l => l.2) c) = d
      rw [hp] at h
      obtain _ | ⟨l,_ | ⟨m,r⟩⟩ := d
      · simp at h
      · simp at h
      · have hh := (pairs_spec φ [(l.1,true),(m.1,true)]).mpr ⟨c,hc,l,m,r,hp,rfl⟩
        simp [he] at hh
  | cons p ps =>
      have hm : p ∈ hornPairs φ := he.symm ▸ List.mem_cons_self
      obtain ⟨c,hc,l,m,r,hr,hp⟩ := (pairs_spec φ p).mp hm
      have hk : hornKeys φ = [l.1,m.1] := by simp [hornKeys,he,hp,List.headD]
      refine ⟨?_,by simp [hk],?_⟩
      · simp only [hk,List.cons_ne_nil,false_iff]
        intro h
        have h1 := h c hc
        rw [hr] at h1
        simp at h1
      · intro xs h _
        by_cases hl : l.1 ∈ xs
        · exact ⟨l.1,by simp [hk],hl⟩
        · by_cases hm : m.1 ∈ xs
          · exact ⟨m.1,by simp [hk],hm⟩
          · have hh := h c hc
            have hfilter :
                c.filter (fun l => l.2 && decide (l.1 ∉ xs)) =
                (c.filter (fun l => l.2)).filter (fun l => decide (l.1 ∉ xs)) := by
              simp only [List.filter_filter,Bool.and_comm]
            rw [hfilter,hr] at hh
            simp [hl,hm] at hh

private def keepPos (w : List Bool) : List Bool := if w.tail.headD false then w else []

private theorem keepPos_cpt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) keepPos := by
  refine cptE (cpt_sel (cpt_hd1 (cpt_tail1 cpt_id)) (cpt_const []) cpt_id) (fun w => ?_)
  unfold keepPos
  cases w with
  | nil => rfl
  | cons b w =>
      cases w with
      | nil => rfl
      | cons b' w => cases b' <;> rfl

private theorem keepPos_spec (l : Literal) :
    keepPos (encodeLiteral l) = if l.2 then encodeLiteral l else [] := by
  rw [encodeLiteral_eq]
  rfl

private def firstTwo (w : List Bool) : List Bool :=
  if (dropI w).headD false then headI w ++ headI (dropI w) ++ [false,false] else []

private theorem firstTwo_cpt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) firstTwo := by
  refine cptE (cpt_sel (cpt_hd1 cpt_dropI) (cpt_const [])
    (cpt_app2 (cpt_app2 cpt_headI (cpt_comp cpt_dropI cpt_headI)) (cpt_const [false,false]))) (fun w => ?_)
  unfold firstTwo
  cases dropI w with
  | nil => rfl
  | cons b r => cases b <;> rfl

private theorem firstTwo_clause (c : Clause) :
    firstTwo (encodeClause c) = match c with
      | l :: m :: _ => encodeClause [l,m]
      | _ => [] := by
  cases c with
  | nil => rfl
  | cons l c =>
      have he : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      rw [firstTwo,he,dropI_lit,headI_lit]
      cases c with
      | nil => rfl
      | cons m r =>
          have hm : encodeClause (m :: r) = encodeLiteral m ++ encodeClause r := by simp [encodeClause]
          rw [hm,headI_lit]
          have h : (encodeLiteral m ++ encodeClause r).headD false = true := by simp [encodeLiteral_eq]
          rw [h]
          simp [encodeClause,List.append_assoc]

private theorem positive_scan (c : Clause) :
    (c.flatMap (fun l => keepPos (encodeLiteral l))) ++ [false,false] =
      encodeClause (c.filter (fun l => l.2)) := by
  have h : c.flatMap (fun l => keepPos (encodeLiteral l)) = (c.filter (fun l => l.2)).flatMap encodeLiteral := by
    simp only [keepPos_spec]
    induction c with
    | nil => rfl
    | cons l r ih => cases h : l.2 <;> simp only [List.flatMap_cons,List.filter_cons,keepPos_spec,h,
        Bool.false_eq_true,ite_false,ite_true,List.nil_append,ih]
  rw [h]
  rfl

/-- Find two positive occurrences in the first clause that violates Horn
shape. The empty clause code is returned exactly when there is no violation. -/
theorem MeasuredHornObstruction :
    ∃ select : CNF → List ℕ, ∃ pick : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pick ∧
      (∀ φ, pick (encodeCNF φ) = encodeClause ((select φ).map (fun x => (x,true)))) ∧
      (∀ φ, select φ = [] ↔ ∀ c ∈ φ, (c.filter (fun l => l.2)).length ≤ 1) ∧
      (∀ φ, (select φ).length ≤ 2) ∧
      ∀ (φ : CNF) (xs : List ℕ), (∀ c ∈ φ, (c.filter (fun l => l.2 && decide (l.1 ∉ xs))).length ≤ 1) →
        select φ ≠ [] → ∃ x ∈ select φ, x ∈ xs := by
  obtain ⟨pos,hpos,hps⟩ := MeasuredLiteralMap (fun p => keepPos p.2) (cpt_comp cpt_snd keepPos_cpt)
  let choose := fun p : List Bool × List Bool => firstTwo (pos p ++ [false,false])
  have hc : ComputableInPolyTime encodePair (fun x : List Bool => x) choose := by
    have hraw := cpt_app2 (cpt_comp (cpt_pair cpt_unpairB1 cpt_unpairB2) hpos) (cpt_const [false,false])
    have h := cpt_comp cpt_pairB (cpt_comp (g := firstTwo) hraw firstTwo_cpt)
    simpa [choose,unpairB_pairB] using h
  obtain ⟨collect,hcol,hcs⟩ := MeasuredClauseMap choose hc
  obtain ⟨split,hsp,_,hss⟩ := measuredFirstClause_reassembles
  let candidates := fun x => collect ([],x)
  let pick := fun x => sel (candidates x) (encodeClause []) (split (candidates x)).1
  have hcan := cpt_comp (cpt_pair (cpt_const []) cpt_id) hcol
  have hpk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pick :=
    cpt_sel hcan (cpt_const (encodeClause [])) (cpt_comp (cpt_comp hcan hsp) cpt_fst)
  refine ⟨hornKeys,pick,hpk,?_,fun φ => (hornKeys_characterize φ).1,
    fun φ => (hornKeys_characterize φ).2.1,fun φ => (hornKeys_characterize φ).2.2⟩
  intro φ
  have hchoose (c : Clause) : choose ([],encodeClause c) =
      match c.filter (fun l => l.2) with
      | l :: m :: _ => encodeClause [(l.1,true),(m.1,true)]
      | _ => [] := by
    unfold choose
    simp only [hps,positive_scan,firstTwo_clause]
    generalize h : c.filter (fun l => l.2) = d
    cases d with
    | nil => rfl
    | cons l d =>
        cases d with
        | nil => rfl
        | cons m r =>
            have hl : l.2 = true := by
              have hmem : l ∈ c.filter (fun l => l.2) := h.symm ▸ List.mem_cons_self
              exact (List.mem_filter.mp hmem).2
            have hm : m.2 = true := by
              have hmem : m ∈ c.filter (fun l => l.2) := h.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self
              exact (List.mem_filter.mp hmem).2
            have el : l = (l.1,true) := Prod.ext rfl hl
            have em : m = (m.1,true) := Prod.ext rfl hm
            change encodeClause [l,m] = encodeClause [(l.1,true),(m.1,true)]
            rw [← el,← em]
  have hrows : candidates (encodeCNF φ) = encodeCNF (hornPairs φ) := by
    simp only [candidates,hcs,hchoose]
    unfold hornPairs
    induction φ with
    | nil => rfl
    | cons c φ ih =>
        unfold encodeCNF at ih ⊢
        rw [List.flatMap_cons,List.filterMap_cons,ih]
        generalize (c.filter (fun l => l.2)) = d
        obtain _ | ⟨l,_ | ⟨m,r⟩⟩ := d <;> rfl
  unfold pick
  rw [hrows]
  cases h : hornPairs φ with
  | nil => simp [sel,encodeCNF,hornKeys,h]
  | cons c cs =>
      have hm : c ∈ hornPairs φ := h.symm ▸ List.mem_cons_self
      obtain ⟨_,_,l,m,_,_,rfl⟩ := (pairs_spec φ c).mp hm
      have he : encodeCNF ([(l.1,true),(m.1,true)] :: cs) =
          encodeClause [(l.1,true),(m.1,true)] ++ encodeCNF cs := by simp [encodeCNF]
      rw [he,sel,ite_eq_right]
      · rw [hss]
        simp [hornKeys,h]
      · simp [encodeClause]

end PEqualNP.Outside
