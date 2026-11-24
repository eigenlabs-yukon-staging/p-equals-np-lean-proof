import PEqualNP.Defs

namespace PEqualNP.Outside.UniqueTernaryGadget
open PEqualNP.Search

def gadget : CNF :=
 [[(0,false),(2,true),(3,true)],
  [(0,true),(2,false),(6,false)],
  [(0,true),(2,true),(6,false)],
  [(0,false),(5,false),(6,false)],
  [(1,false),(3,false),(4,false)],
  [(1,false),(3,true),(4,false)],
  [(1,true),(4,false),(5,true)],
  [(1,false),(4,true),(6,true)],
  [(1,true),(5,false),(6,true)],
  [(2,false),(3,true),(5,true)],
  [(3,false),(4,true),(5,true)]]

theorem shape :
    ∀ c ∈ gadget, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < 7 := by decide

theorem degree (i : ℕ) (hi : i < 7) :
    (gadget.flatMap (List.map Prod.fst)).count i = if i = 0 ∨ i = 2 then 4 else 5 := by
  interval_cases i <;> decide

theorem zero_model : CNF.eval (fun _ => false) gadget = true := by decide

private def onFin (a : Fin 7 → Bool) : Assignment :=
  fun i => if h : i < 7 then a ⟨i,h⟩ else false

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
private theorem unique_fin :
    ∀ a : Fin 7 → Bool, CNF.eval (onFin a) gadget = true → ∀ i, a i = false := by
  decide

theorem unique (a : Assignment) (h : CNF.eval a gadget = true) :
    ∀ i < 7, a i = false := by
  let b : Fin 7 → Bool := fun i => a i.1
  have hb : CNF.eval (onFin b) gadget = true := by
    simpa [onFin,b,gadget,CNF.eval,Clause.eval,Literal.eval] using h
  exact fun i hi => unique_fin b hb ⟨i,hi⟩

end PEqualNP.Outside.UniqueTernaryGadget

open PEqualNP.Search

theorem PEqualNP.Outside.UniqueTernaryFalseGadget :
    ∃ G : CNF,
      (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < 7) ∧
      (∀ i < 7, (G.flatMap (List.map Prod.fst)).count i = if i = 0 ∨ i = 2 then 4 else 5) ∧
      CNF.eval (fun _ => false) G = true ∧
      (∀ a : Assignment, CNF.eval a G = true → ∀ i < 7, a i = false) := by
  open PEqualNP.Outside.UniqueTernaryGadget in
  exact ⟨gadget,shape,degree,zero_model,unique⟩
