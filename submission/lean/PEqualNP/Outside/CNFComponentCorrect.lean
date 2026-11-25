import PEqualNP.Library.SearchHelpers.TwoSat
import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside

open PEqualNP.Search
open PEqualNP.Library.SearchHelpers.TwoSat

def touches (φ : CNF) (x y : ℕ) : Prop :=
  ∃ c ∈ φ, x ∈ c.map Prod.fst ∧ y ∈ c.map Prod.fst

abbrev connected (φ : CNF) : ℕ → ℕ → Prop := Relation.ReflTransGen (touches φ)

def variableGraph (φ : CNF) : CNF :=
  φ.flatMap (fun c => c.flatMap (fun l => c.map (fun m => [(l.1,false),(m.1,true)])))

theorem graph_binary (φ : CNF) (c : Clause) (h : c ∈ variableGraph φ) : c.length = 2 := by
  simp only [variableGraph,List.mem_flatMap,List.mem_map] at h
  obtain ⟨_,_,l,_,m,_,rfl⟩ := h
  rfl

private theorem graph_pos_step (φ : CNF) (x : ℕ) (y : Literal) :
    Edge (variableGraph φ) (x,true) y ↔ y.2 = true ∧ touches φ x y.1 := by
  constructor
  · rintro ⟨d,hd,hy⟩
    simp only [variableGraph,List.mem_flatMap,List.mem_map] at hd
    obtain ⟨c,hc,l,hl,m,hm,rfl⟩ := hd
    apply (mem_forced_single _ _ _).mp at hy
    rcases hy with ⟨h,_⟩ | ⟨a,h,hu⟩
    · simp at h
    · rcases h with ha | ha
      · have h₁ : (l.1,false) = a ∧ (m.1,true) = y := by simpa using ha
        obtain ⟨rfl,rfl⟩ := h₁
        have hx : x = l.1 := by simpa [neg] using hu
        exact ⟨rfl,⟨c,hc,List.mem_map.mpr ⟨l,hl,hx.symm⟩,List.mem_map.mpr ⟨m,hm,rfl⟩⟩⟩
      · have ha' : (l.1,false) = y ∧ (m.1,true) = a := by simpa using ha
        obtain ⟨rfl,rfl⟩ := ha'
        simp [neg] at hu
  · rintro ⟨hy,⟨c,hc,hx,hy'⟩⟩
    obtain ⟨l,hl,he⟩ := List.mem_map.mp hx
    obtain ⟨m,hm,he'⟩ := List.mem_map.mp hy'
    have hyy : y = (m.1,true) := Prod.ext he'.symm hy
    refine ⟨[(l.1,false),(m.1,true)],List.mem_flatMap.mpr ⟨c,hc,
      List.mem_flatMap.mpr ⟨l,hl,List.mem_map.mpr ⟨m,hm,rfl⟩⟩⟩,?_⟩
    rw [hyy,← he]
    simp [forced,neg]

theorem graph_reach (φ : CNF) (x y : ℕ) :
    Reach (variableGraph φ) (x,true) (y,true) ↔ connected φ x y := by
  constructor
  · intro h
    have lift {a : Literal} (ha : Reach (variableGraph φ) (x,true) a) :
        a.2 = true ∧ connected φ x a.1 := by
      induction ha with
      | refl => exact ⟨rfl,.refl⟩
      | @tail mid out _ he ih =>
          have hm : mid = (mid.1,true) := Prod.ext rfl ih.1
          rw [hm,graph_pos_step] at he
          exact ⟨he.1,ih.2.tail he.2⟩
    exact (lift h).2
  · intro h
    induction h with
    | refl => exact .refl
    | @tail m z _ he ih =>
        exact ih.tail ((graph_pos_step φ m (z,true)).mpr ⟨rfl,he⟩)

theorem connected_symm (φ : CNF) {x y : ℕ} (h : connected φ x y) : connected φ y x := by
  induction h with
  | refl => exact .refl
  | tail _ he ih =>
      obtain ⟨c,hc,hx,hy⟩ := he
      exact Relation.ReflTransGen.head ⟨c,hc,hy,hx⟩ ih

noncomputable def component (φ : CNF) (x : ℕ) : CNF :=
  φ.filter (fun c => @decide (∃ l ∈ c, connected φ x l.1) (Classical.propDecidable _))

theorem mem_component {φ : CNF} {x : ℕ} {c : Clause} :
    c ∈ component φ x ↔ c ∈ φ ∧ ∃ l ∈ c, connected φ x l.1 := by
  classical
  simp [component]

theorem component_agree {φ : CNF} {x y : ℕ} (h : connected φ x y) :
    component φ x = component φ y := by
  classical
  unfold component
  apply List.filter_congr
  intro c _
  exact @Bool.decide_congr _ _ (Classical.propDecidable _) (Classical.propDecidable _) ⟨
    fun ⟨l,hl,he⟩ => ⟨l,hl,(connected_symm φ h).trans he⟩,
    fun ⟨l,hl,he⟩ => ⟨l,hl,h.trans he⟩⟩

theorem component_first {φ : CNF} {x : ℕ} (l : Literal) (c : Clause) (hc : l :: c ∈ φ) :
    l :: c ∈ component φ x ↔ connected φ x l.1 := by
  rw [mem_component]
  constructor
  · rintro ⟨_,m,hm,hr⟩
    exact hr.tail ⟨l :: c,hc,List.mem_map.mpr ⟨m,hm,rfl⟩,List.mem_map.mpr ⟨l,List.mem_cons_self,rfl⟩⟩
  · exact fun h => ⟨hc,l,List.mem_cons_self,h⟩

private noncomputable def representative (φ : CNF) (x : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ y, connected φ x y from ⟨x,.refl⟩)

private theorem representative_reach (φ : CNF) (x : ℕ) : connected φ x (representative φ x) := by
  classical
  unfold representative
  exact Nat.find_spec (show ∃ y, connected φ x y from ⟨x,.refl⟩)

private theorem representative_same (φ : CNF) (x y : ℕ) (h : connected φ x y) :
    representative φ x = representative φ y := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' _ (h.trans (representative_reach φ y))
  · exact Nat.find_min' _ ((connected_symm φ h).trans (representative_reach φ x))

/-- Satisfiability decomposes over the variable co-occurrence classes. -/
theorem components_sat_iff (φ : CNF) :
    Satisfiable φ ↔ [] ∉ φ ∧ ∀ x, Satisfiable (component φ x) := by
  classical
  constructor
  · rintro ⟨σ,hσ⟩
    simp only [CNF.eval,List.all_eq_true] at hσ
    constructor
    · intro h
      exact Bool.false_ne_true (hσ [] h)
    · intro x
      exact ⟨σ,List.all_eq_true.mpr (fun c hc => hσ c (mem_component.mp hc).1)⟩
  · rintro ⟨hne,hall⟩
    choose σ hσ using hall
    refine ⟨fun x => σ (representative φ x) x, List.all_eq_true.mpr (fun c hc => ?_)⟩
    cases c with
    | nil => exact (hne hc).elim
    | cons l ls =>
        have hl : l :: ls ∈ component φ (representative φ l.1) :=
          (component_first l ls hc).mpr (connected_symm φ (representative_reach φ l.1))
        obtain ⟨m,hm,hv⟩ := List.any_eq_true.mp (List.all_eq_true.mp (hσ (representative φ l.1)) _ hl)
        have hreach : connected φ m.1 l.1 :=
          .single ⟨l :: ls,hc,List.mem_map.mpr ⟨m,hm,rfl⟩,List.mem_map.mpr ⟨l,List.mem_cons_self,rfl⟩⟩
        apply List.any_eq_true.mpr
        refine ⟨m,hm,?_⟩
        simpa [Literal.eval,representative_same φ m.1 l.1 hreach] using hv

theorem components_sat_from_heads (φ : CNF) (hne : [] ∉ φ)
    (h : ∀ l : Literal, ∀ c : Clause, l :: c ∈ φ → Satisfiable (component φ l.1)) :
    Satisfiable φ := by
  refine (components_sat_iff φ).mpr ⟨hne,fun x => ?_⟩
  cases e : component φ x with
  | nil => exact ⟨fun _ => false,rfl⟩
  | cons c cs =>
      have hc : c ∈ component φ x := e.symm ▸ List.mem_cons_self
      have hφ := (mem_component.mp hc).1
      cases c with
      | nil => exact (hne hφ).elim
      | cons l c =>
          have he := (component_first l c hφ).mp hc
          rw [← e,component_agree he]
          exact h l c hφ

end PEqualNP.Outside
