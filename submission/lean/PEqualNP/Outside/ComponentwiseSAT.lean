import PEqualNP.Outside.MeasuredCNFComponent
import PEqualNP.Library.L046
import PEqualNP.Library.Universal.BruteForce

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard
open PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Search

private def passes (get : List Bool × List Bool → List Bool) (d : List Bool → Bool)
    (p : List Bool × List Bool) : Bool :=
  p.2.headD false && d (get (headI p.2,p.1))

private theorem failing_clause_cpt {get : List Bool × List Bool → List Bool}
    {d : List Bool → Bool}
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) get)
    (hd' : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool d) :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p => if passes get d p then [] else [true]) := by
  have hc := cpt_comp (cpt_pair (cpt_comp cpt_unpairB2 cpt_headI) cpt_unpairB1) hg
  have hb := cpt_bitFlag (cpt_comp hc hd')
  have hs := cpt_sel (cpt_hd1 cpt_unpairB2) (cpt_const [true])
    (cpt_sel hb (cpt_const [true]) (cpt_const []))
  have hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => if passes get d (unpairB s) then [] else [true]) := by
    refine cptE hs (fun s => ?_)
    change sel (hd (unpairB s).2) [true]
      (sel (if d (get (headI (unpairB s).2,(unpairB s).1)) then [true] else []) [true] []) = _
    unfold passes
    cases h : (unpairB s).2 with
    | nil => rfl
    | cons a r =>
        cases a <;> cases e : d (get (headI (_ :: r),(unpairB s).1)) <;> simp [hd,sel,e]
  have hp := cpt_comp cpt_pairB hr
  simpa only [unpairB_pairB] using hp

private theorem heads_iff (φ : CNF) (G : Language Bool) :
    (∀ l c, l :: c ∈ φ → encodeCNF (component φ l.1) ∈ G) ↔
    ∀ c ∈ φ, ∀ l ∈ c, encodeCNF (component φ l.1) ∈ G := by
  constructor
  · intro h c hc l hl
    cases c with
    | nil => simp at hl
    | cons m c =>
        have he : connected φ l.1 m.1 := .single ⟨m :: c,hc,
          List.mem_map.mpr ⟨l,hl,rfl⟩,List.mem_map.mpr ⟨m,List.mem_cons_self,rfl⟩⟩
        rw [component_agree he]
        exact h m c hc
  · intro h l c hl
    exact h (l :: c) hl l List.mem_cons_self

/-- Any measured guarded SAT algorithm lifts to a measured algorithm on
canonical CNFs all of whose variable components are in the guard. -/
theorem ComponentwiseSAT (G D : Language Bool) (hG : G ∈ P) (hD : D ∈ P)
    (hSpec : ∀ φ : CNF, encodeCNF φ ∈ G → (encodeCNF φ ∈ D ↔ Satisfiable φ)) :
    let part := fun (φ : CNF) (x : ℕ) => φ.filter (fun c =>
      @decide (∃ m ∈ c, Relation.ReflTransGen (fun a b : ℕ =>
        ∃ d ∈ φ, a ∈ d.map Prod.fst ∧ b ∈ d.map Prod.fst) x m.1) (Classical.propDecidable _))
    {s : List Bool | ∃ φ : CNF, encodeCNF φ = s ∧
      (∀ c ∈ φ, ∀ l ∈ c, encodeCNF (part φ l.1) ∈ G) ∧ Satisfiable φ} ∈ P := by
  classical
  obtain ⟨get,hget,hgs⟩ := MeasuredCNFComponent
  obtain ⟨d,hd,hcd⟩ := L046 G D hG hD
  let fail := fun p : List Bool × List Bool => if passes get d p then [] else [true]
  obtain ⟨collect,hc,hcs⟩ := MeasuredClauseMap fail (failing_clause_cpt hget hcd)
  let out := fun x => collect (x,x)
  let accept := fun x => wfB x && (out x).isEmpty
  have hout := cpt_comp (cpt_pair cpt_id cpt_id) hc
  have ht := cpt_comp (g := fun w : List Bool => !w.isEmpty)
    (cpt_sel cpt_wfF (cpt_const []) (cpt_sel hout (cpt_const [true]) (cpt_const []))) bf_cpt_neL
  have he : (fun x => !(sel (bflag (wfB x)) [] (sel (out x) [true] [])).isEmpty) = accept := by
    funext x
    unfold accept
    cases wfB x <;> cases out x <;> rfl
  rw [he] at ht
  refine ⟨accept,fun x => ?_,ht⟩
  change (∃ φ : CNF, encodeCNF φ = x ∧
    (∀ c ∈ φ, ∀ l ∈ c, encodeCNF (component φ l.1) ∈ G) ∧ Satisfiable φ) ↔ accept x = true
  have hspec (φ : CNF) :
      (out (encodeCNF φ)).isEmpty = true ↔
        (∀ c ∈ φ, ∀ l ∈ c, encodeCNF (component φ l.1) ∈ G) ∧ Satisfiable φ := by
    have hlocal (p : CNF) : d (encodeCNF p) = true ↔ encodeCNF p ∈ G ∧ Satisfiable p := by
      rw [← hd]
      change (encodeCNF p ∈ G ∧ encodeCNF p ∈ D) ↔ (encodeCNF p ∈ G ∧ Satisfiable p)
      exact and_congr_right (hSpec p)
    have hnil : fail (encodeCNF φ,encodeClause []) = [true] := by simp [fail,passes,encodeClause]
    have hone (l : Literal) (c : Clause) :
        fail (encodeCNF φ,encodeClause (l :: c)) = [] ↔
          encodeCNF (component φ l.1) ∈ G ∧ Satisfiable (component φ l.1) := by
      have hc' : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
      have hhead : (encodeLiteral l ++ encodeClause c).headD false = true := by simp [encodeLiteral_eq]
      have hs : get (encodeLiteral l,encodeCNF φ) = encodeCNF (component φ l.1) := hgs l φ
      simp only [fail,passes,hc',hhead,Bool.true_and,headI_lit,hs]
      rw [← hlocal]
      cases d (encodeCNF (component φ l.1)) <;> decide
    change (collect (encodeCNF φ,encodeCNF φ)).isEmpty = true ↔ _
    rw [List.isEmpty_iff,hcs,List.flatMap_eq_nil_iff]
    constructor
    · intro h
      have hne : [] ∉ φ := by
        intro hc
        have := h [] hc
        rw [hnil] at this
        contradiction
      have hl (l : Literal) (c : Clause) (hc : l :: c ∈ φ) :=
        (hone l c).mp (h _ hc)
      exact ⟨(heads_iff φ G).mp (fun l c hm => (hl l c hm).1),
        components_sat_from_heads φ hne (fun l c hm => (hl l c hm).2)⟩
    · rintro ⟨hg,hs⟩ c hc'
      obtain ⟨hne,hall⟩ := (components_sat_iff φ).mp hs
      cases c with
      | nil => exact (hne hc').elim
      | cons l c => exact (hone l c).mpr ⟨hg _ hc' l List.mem_cons_self,hall l.1⟩
  unfold accept
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨φ,rfl,hg,hs⟩
    exact ⟨(wfB_iff _).mpr ⟨φ,rfl⟩,(hspec φ).mpr ⟨hg,hs⟩⟩
  · rintro ⟨hcanon,hall⟩
    obtain ⟨φ,rfl⟩ := (wfB_iff _).mp hcanon
    exact ⟨φ,rfl,(hspec φ).mp hall⟩

end PEqualNP.Outside
