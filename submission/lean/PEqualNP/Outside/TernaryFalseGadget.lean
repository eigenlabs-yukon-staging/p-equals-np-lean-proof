import PEqualNP.Defs

namespace PEqualNP.Outside.TernaryGadget
open PEqualNP.Search

def gadget : CNF :=
  [[(0,false),(1,false),(2,false)],
   [(0,false),(1,true),(3,true)],
   [(0,false),(2,true),(3,false)],
   [(1,false),(2,true),(3,true)],
   [(1,true),(2,false),(3,false)]]

theorem forced (σ : Assignment) (h : CNF.eval σ gadget = true) : σ 0 = false := by
  cases h0 : σ 0
  · rfl
  · cases h1 : σ 1 <;> cases h2 : σ 2 <;> cases h3 : σ 3 <;>
      simp [gadget,CNF.eval,Clause.eval,Literal.eval,h0,h1,h2,h3] at h

theorem zero_model : CNF.eval (fun _ => false) gadget = true := by decide

theorem shape :
    ∀ c ∈ gadget, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < 4 := by decide

theorem degree (i : ℕ) (hi : i < 4) :
    (gadget.flatMap (List.map Prod.fst)).count i = if i = 0 then 3 else 4 := by
  interval_cases i <;> decide

def evalFin (a : Fin 4 → Bool) : Bool :=
  CNF.eval (fun i => if h : i < 4 then a ⟨i,h⟩ else false) gadget

theorem six_models :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun a => evalFin a = true)).card = 6 := by
  decide

end PEqualNP.Outside.TernaryGadget

open PEqualNP.Search

theorem PEqualNP.Outside.TernaryFalseGadget :
    ∃ G : CNF,
      (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < 4) ∧
      (∀ i < 4, (G.flatMap (List.map Prod.fst)).count i = if i = 0 then 3 else 4) ∧
      CNF.eval (fun _ => false) G = true ∧
      (∀ a : Assignment, CNF.eval a G = true → a 0 = false) ∧
      ((Finset.univ : Finset (Fin 4 → Bool)).filter
        (fun a => CNF.eval (fun i => if h : i < 4 then a ⟨i,h⟩ else false) G = true)).card = 6 := by
  open PEqualNP.Outside.TernaryGadget in
  exact ⟨gadget,shape,degree,zero_model,forced,six_models⟩
