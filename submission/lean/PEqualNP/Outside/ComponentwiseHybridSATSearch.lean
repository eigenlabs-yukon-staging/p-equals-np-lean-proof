import PEqualNP.Outside.ExactComponentwiseHybridSAT
import PEqualNP.Outside.SparseVariableSATSearch

namespace PEqualNP.Outside

open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Search

private def units (ls : List Literal) : CNF := ls.map (fun l => [l])

private theorem conn_units (φ : CNF) (ls : List Literal) (x y : ℕ) :
    connected (φ ++ units ls) x y ↔ connected φ x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ he ih =>
        obtain ⟨c,hc,hx,hy⟩ := he
        rcases List.mem_append.mp hc with hc | hc
        · exact ih.tail ⟨c,hc,hx,hy⟩
        · unfold units at hc
          obtain ⟨l,_,rfl⟩ := List.mem_map.mp hc
          simp only [List.map_cons,List.map_nil,List.mem_singleton] at hx hy
          rw [hy,← hx]
          exact ih
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ he ih =>
        obtain ⟨c,hc,hx,hy⟩ := he
        exact ih.tail ⟨c,List.mem_append_left _ hc,hx,hy⟩

private theorem component_units (φ : CNF) (ls : List Literal) (x : ℕ) :
    ∃ extra : CNF, extra.Sublist (units ls) ∧ component (φ ++ units ls) x = component φ x ++ extra := by
  let p := fun c : Clause => @decide (∃ m ∈ c, connected (φ ++ units ls) x m.1) (Classical.propDecidable _)
  refine ⟨(units ls).filter p,List.filter_sublist,?_⟩
  simp only [component,List.filter_append]
  apply congrArg (fun a => a ++ (units ls).filter p)
  apply List.filter_congr
  intro c _
  exact @Bool.decide_congr _ _ (Classical.propDecidable _) (Classical.propDecidable _) <|
    ⟨fun ⟨m,hm,he⟩ => ⟨m,hm,(conn_units φ ls x m.1).mp he⟩,
     fun ⟨m,hm,he⟩ => ⟨m,hm,(conn_units φ ls x m.1).mpr he⟩⟩

private theorem nat_eval_mono (q : Polynomial ℕ) : Monotone q.eval := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      intro a b hab
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add (hp hab) (hq hab)
  | monomial i c =>
      intro a b hab
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab _)

private theorem shape_add_units (q : Polynomial ℕ) (p extra : CNF)
    (ls : List Literal) (hsub : extra.Sublist (units ls)) (h : hybridShape q p) :
    hybridShape q (p ++ extra) := by
  have hunit (c : Clause) (hc : c ∈ extra) : c.length = 1 := by
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp (hsub.subset hc)
    rfl
  rcases h with h | ⟨k,hk,xs,hxs,hw⟩
  · left
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h c hc
    · have hlen := List.length_filter_le (fun l : Literal => l.2) c
      rwa [hunit c hc] at hlen
  · right
    have hlen : (encodeCNF p).length ≤ (encodeCNF (p ++ extra)).length := by
      simp only [encodeCNF,List.flatMap_append,List.length_append]
      omega
    refine ⟨k,hk.trans (Nat.add_le_add_right (nat_eval_mono q hlen) _),xs,hxs,fun c hc => ?_⟩
    rw [List.map_append,List.mem_append] at hc
    rcases hc with hc | hc
    · exact hw c hc
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have h := List.length_filter_le (fun l : Literal => decide (l.1 ∉ xs)) d
      rw [hunit d hd] at h
      exact h.trans (by decide)

private theorem all_components (q : Polynomial ℕ) (φ : CNF)
    (h : ∀ c ∈ φ, ∀ l ∈ c, hybridShape q (component φ l.1)) :
    ∀ x, hybridShape q (component φ x) := by
  intro x
  cases he : component φ x with
  | nil => exact Or.inl (by simp)
  | cons c cs =>
      have hc : c ∈ component φ x := he.symm ▸ List.mem_cons_self
      obtain ⟨hφ,l,hl,hx⟩ := mem_component.mp hc
      exact he ▸ component_agree hx ▸ h c hφ l hl

/-- Sparse witness recovery for the hybrid componentwise language. Added unit
clauses only contribute self-edges, so the old component partition persists. -/
theorem ComponentwiseHybridSATSearch (q : Polynomial ℕ) :
    let part := fun (φ : CNF) (x : ℕ) => φ.filter (fun c =>
      @decide (∃ m ∈ c, Relation.ReflTransGen (fun a b : ℕ =>
        ∃ d ∈ φ, a ∈ d.map Prod.fst ∧ b ∈ d.map Prod.fst) x m.1) (Classical.propDecidable _))
    ∃ search : List Bool → List Bool,
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) search ∧
      ∀ φ : CNF, (∀ c ∈ φ, ∀ l ∈ c,
        let p := part φ l.1
        (∀ d ∈ p, (d.filter (fun m => m.2)).length ≤ 1) ∨
        (∃ k : ℕ, 6^k ≤ q.eval (encodeCNF p).length + 1 ∧ ∃ xs : List ℕ, xs.length ≤ k ∧
          IsKCNF 2 (p.map (fun d => d.filter (fun m => decide (m.1 ∉ xs)))))) →
        Satisfiable φ → ∃ vs : List ℕ,
          search (encodeCNF φ) = vs.flatMap (fun i => (i.bits.flatMap fun b => [true,b]) ++ [false,true]) ∧
          (search (encodeCNF φ)).length ≤ (encodeCNF φ).length ∧
          CNF.eval (fun i => decide (i ∈ vs)) φ = true := by
  let D : Language Bool := {s | ∃ φ : CNF, encodeCNF φ = s ∧
    (∀ c ∈ φ, ∀ l ∈ c, hybridShape q (component φ l.1)) ∧ Satisfiable φ}
  obtain ⟨search,hs,hc⟩ := SparseVariableSATSearch D (ExactComponentwiseHybridSAT q)
  refine ⟨search,hs,fun φ h => hc φ (fun ls => ?_)⟩
  let ψ := φ ++ units ls
  change encodeCNF ψ ∈ D ↔ Satisfiable ψ
  constructor
  · rintro ⟨f,hf,_,hs⟩
    exact encodeCNF_injective hf ▸ hs
  · intro hs
    refine ⟨ψ,rfl,fun c _ l _ => ?_,hs⟩
    obtain ⟨extra,hextra,he⟩ := component_units φ ls l.1
    rw [he]
    exact shape_add_units q _ extra ls hextra (all_components q φ h l.1)

end PEqualNP.Outside
