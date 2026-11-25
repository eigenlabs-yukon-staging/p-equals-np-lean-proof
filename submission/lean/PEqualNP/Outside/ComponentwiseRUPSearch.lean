import PEqualNP.Outside.MeasuredCNFComponent
import PEqualNP.Outside.MeasuredBoundedRUPCheck
import PEqualNP.Outside.RUPRunMonotone
import PEqualNP.Library.SearchHelpers.Encoding

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.KSat.Hard PEqualNP.Search

private abbrev Raw := List Bool

def boundedRefutation (φ : CNF) (w : Raw) : Prop :=
  w.length ≤ 2*(encodeCNF φ).length+6 ∧
    ∃ ρ : CNF, encodeCNF ρ = w ∧ IsRUPRun (clauseSet φ) (ρ.map List.toFinset) ∧ [] ∈ ρ

private theorem certified_nonempty {φ : CNF} {w : Raw} (h : boundedRefutation φ w) : w ≠ [] := by
  obtain ⟨_,ρ,rfl,_,he⟩ := h
  intro hn
  have eq := encodeCNF_injective (hn.trans (show [] = encodeCNF [] by rfl))
  simp [eq] at he

private theorem certified_unsat {φ : CNF} {w : Raw} (h : boundedRefutation φ w) : ¬ Satisfiable φ := by
  obtain ⟨_,ρ,_,hr,he⟩ := h
  exact rup_run_refutes φ ρ hr he

private theorem empty_trace (φ : CNF) (he : [] ∈ φ) : boundedRefutation φ (encodeCNF [[]]) := by
  have hlen : (encodeCNF ([[]] : CNF)).length = 2 := rfl
  refine ⟨by omega,[[]],rfl,?_,by simp⟩
  apply (rup_run_cons φ [] []).mpr
  have hv : IsRUP (clauseSet φ) ([] : Clause).toFinset := by
    refine ⟨∅,⟨[],he,rfl⟩,?_⟩
    simp
  exact ⟨by simpa only [List.append_nil] using hv,.nil⟩

private theorem lift_trace (φ : CNF) (x : ℕ) (w : Raw)
    (h : boundedRefutation (component φ x) w) : boundedRefutation φ w := by
  obtain ⟨hlen,ρ,he,hr,h0⟩ := h
  have hsub : (component φ x).Sublist φ := by
    unfold component
    exact List.filter_sublist
  have hlen' : (encodeCNF (component φ x)).length ≤ (encodeCNF φ).length :=
    (hsub.flatMap encodeClause).length_le
  have hcl : clauseSet (component φ x) ⊆ clauseSet φ := by
    rintro d ⟨c,hc,rfl⟩
    exact ⟨c,hsub.subset hc,rfl⟩
  exact ⟨by omega,ρ,he,RUPRunMonotone hcl _ hr,h0⟩

theorem measured_bounded_refutation :
    ∃ check : Raw × Raw → Bool,
      ComputableInPolyTime encodePair Computability.encodeBool check ∧
      ∀ (φ : CNF) (w : Raw), check (encodeCNF φ,w) = true ↔ boundedRefutation φ w := by
  let q : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 6
  obtain ⟨check,hv,hc⟩ := MeasuredBoundedRUPCheck q
  refine ⟨check,hc,fun φ w => ?_⟩
  rw [← hv]
  change (w.length ≤ q.eval (encodeCNF φ).length ∧
    ∃ ψ ρ : CNF, encodeCNF ψ = encodeCNF φ ∧ encodeCNF ρ = w ∧
      IsRUPRun (clauseSet ψ) (ρ.map List.toFinset) ∧ [] ∈ ρ) ↔ _
  simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,boundedRefutation]
  constructor
  · rintro ⟨hlen,ψ,ρ,hEq,he,hr,h0⟩
    have hp := encodeCNF_injective hEq
    exact ⟨hlen,ρ,he,hp ▸ hr,h0⟩
  · rintro ⟨hlen,ρ,he,hr,h0⟩
    exact ⟨hlen,φ,ρ,rfl,he,hr,h0⟩

private def record (w : Raw) : Raw := pairB w []

private def scanClause (gen : Raw → Raw) (get : Raw × Raw → Raw) (check : Raw × Raw → Bool)
    (p : Raw × Raw) : Raw :=
  let w := gen (get (headI p.2,p.1))
  if p.2.headD false then (if check (p.1,w) then record w else [])
  else record (encodeCNF [[]])

private theorem scan_cpt {gen : Raw → Raw} {get : Raw × Raw → Raw} {check : Raw × Raw → Bool}
    (hg : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) gen)
    (he : ComputableInPolyTime encodePair (fun x : Raw => x) get)
    (hc : ComputableInPolyTime encodePair Computability.encodeBool check) :
    ComputableInPolyTime encodePair (fun x : Raw => x) (scanClause gen get check) := by
  have hgen := cpt_comp (cpt_comp (cpt_pair (cpt_comp cpt_unpairB2 cpt_headI) cpt_unpairB1) he) hg
  have ht := cpt_bitFlag (cpt_comp (cpt_pair cpt_unpairB1 hgen) hc)
  have hw := cpt_pairB2 hgen (cpt_const [])
  have h := cpt_sel (cpt_hd1 cpt_unpairB2) (cpt_const (record (encodeCNF [[]]))) (cpt_sel ht (cpt_const []) hw)
  have hs : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x)
      (fun s => scanClause gen get check (unpairB s)) := by
    refine PEqualNP.Library.SearchHelpers.Tab.StepW.cptE h (fun x => ?_)
    change sel (hd (unpairB x).2) (record (encodeCNF [[]]))
      (sel (if check ((unpairB x).1,gen (get (headI (unpairB x).2,(unpairB x).1))) then [true] else [])
        [] (record (gen (get (headI (unpairB x).2,(unpairB x).1))))) = _
    unfold scanClause
    cases h2 : (unpairB x).2 with
    | nil => rfl
    | cons b r =>
        cases b <;> cases e : check ((unpairB x).1,gen (get (headI (_ :: r),(unpairB x).1))) <;>
          simp [hd,sel,e]
  have hp := cpt_comp cpt_pairB hs
  simpa only [unpairB_pairB] using hp

private theorem first_cert (φ : CNF) (xs : List Raw)
    (h : ∀ w ∈ xs, w = [] ∨ ∃ z, w = record z ∧ boundedRefutation φ z) :
    (((unpairB xs.flatten).1 = []) ↔ xs.flatten = []) ∧
      ((unpairB xs.flatten).1 ≠ [] → boundedRefutation φ (unpairB xs.flatten).1) := by
  induction xs with
  | nil => simp [unpairB]
  | cons w xs ih =>
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rcases h w List.mem_cons_self with rfl | ⟨z,rfl,hz⟩
      · simpa using ht
      · have hp : record z ++ xs.flatten = pairB z xs.flatten := by
          simp [record,pairB,List.append_assoc]
        have hu : pairB z xs.flatten ≠ [] := by simp [pairB]
        simp only [List.flatten_cons,hp,unpairB_pairB]
        exact ⟨iff_of_false (certified_nonempty hz) hu,fun _ => hz⟩

/-- Lift a measured local RUP trace generator to variable components.
Every nonempty emitted result is a checked, bounded global refutation. -/
theorem ComponentwiseRUPSearch (gen : List Bool → List Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) gen) :
    let part := fun (φ : CNF) (x : ℕ) => φ.filter (fun c =>
      @decide (∃ m ∈ c, Relation.ReflTransGen (fun a b : ℕ =>
        ∃ d ∈ φ, a ∈ d.map Prod.fst ∧ b ∈ d.map Prod.fst) x m.1) (Classical.propDecidable _))
    let valid := fun (φ : CNF) (w : List Bool) =>
      w.length ≤ 2*(encodeCNF φ).length+6 ∧ ∃ ρ : CNF, encodeCNF ρ = w ∧
        IsRUPRun {d : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, c.toFinset = d}
          (ρ.map fun c => c.toFinset) ∧ [] ∈ ρ
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF,
        (search (encodeCNF φ) ≠ [] → valid φ (search (encodeCNF φ))) ∧
        ((∀ l : Literal, ∀ c : Clause, l :: c ∈ φ → ¬ Satisfiable (part φ l.1) →
          valid (part φ l.1) (gen (encodeCNF (part φ l.1)))) →
          (search (encodeCNF φ) = [] ↔ Satisfiable φ)) := by
  classical
  obtain ⟨get,he,hes⟩ := MeasuredCNFComponent
  obtain ⟨check,hc,hcs⟩ := measured_bounded_refutation
  obtain ⟨collect,ht,hts⟩ := MeasuredClauseMap (scanClause gen get check) (scan_cpt hg he hc)
  let search := fun x => (unpairB (collect (x,x))).1
  have hsearch : ComputableInPolyTime (fun x : Raw => x) (fun x : Raw => x) search :=
    cpt_unpairB1_1 (cpt_comp (cpt_pair cpt_id cpt_id) ht)
  refine ⟨search,hsearch,fun φ => ?_⟩
  let one := fun c => scanClause gen get check (encodeCNF φ,encodeClause c)
  have hcollect : collect (encodeCNF φ,encodeCNF φ) = (φ.map one).flatten := by
    rw [hts]
    rfl
  have hrow (l : Literal) (c : Clause) :
      one (l :: c) = if check (encodeCNF φ,gen (encodeCNF (component φ l.1))) then
        record (gen (encodeCNF (component φ l.1))) else [] := by
    have hcode : encodeClause (l :: c) = encodeLiteral l ++ encodeClause c := by simp [encodeClause]
    have ht : (encodeLiteral l ++ encodeClause c).headD false = true := by simp [encodeLiteral_eq]
    have he : get (encodeLiteral l,encodeCNF φ) = encodeCNF (component φ l.1) := hes l φ
    simp only [one,scanClause,hcode,ht,ite_true,headI_lit,he]
  have hnil : one [] = record (encodeCNF [[]]) := rfl
  have hs (x : Raw) (hx : x ∈ φ.map one) :
      x = [] ∨ ∃ z, x = record z ∧ boundedRefutation φ z := by
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hx
    cases c with
    | nil => exact Or.inr ⟨_,hnil,empty_trace φ hc'⟩
    | cons l c =>
        rw [hrow]
        split
        · rename_i h
          exact Or.inr ⟨_,rfl,(hcs φ _).mp h⟩
        · exact Or.inl rfl
  have hfirst := first_cert φ (φ.map one) hs
  have hcert : search (encodeCNF φ) ≠ [] → boundedRefutation φ (search (encodeCNF φ)) := by
    simp only [search,hcollect]
    exact hfirst.2
  refine ⟨hcert,fun hcover => ⟨?_,?_⟩⟩
  · intro hzero
    have hflat : (φ.map one).flatten = [] := hfirst.1.mp (by simpa [search,hcollect] using hzero)
    have hall (c : Clause) (hc : c ∈ φ) : one c = [] := by
      have h : φ.flatMap one = [] := hflat
      exact (List.flatMap_eq_nil_iff.mp h) c hc
    have h0 : [] ∉ φ := by
      intro h
      have ht := hall [] h
      rw [hnil] at ht
      simp [record,pairB] at ht
    apply components_sat_from_heads φ h0
    intro l c hmem
    by_contra hns
    have h : boundedRefutation φ (gen (encodeCNF (component φ l.1))) :=
      lift_trace φ l.1 _ (hcover l c hmem hns)
    have hv : check (encodeCNF φ,gen (encodeCNF (component φ l.1))) = true := (hcs φ _).mpr h
    have hx := hall (l :: c) hmem
    rw [hrow,if_pos hv] at hx
    simp [record,pairB] at hx
  · intro hs
    by_contra hn
    exact certified_unsat (hcert hn) hs

end PEqualNP.Outside
