import PEqualNP.Defs

namespace PEqualNP.Outside.DegreeFill
open PEqualNP.Search

def gadget : CNF :=
  [[(0,true),(1,true),(2,true)],
   [(3,true),(4,true),(5,true)],
   [(2,true),(4,true),(5,true)],
   [(2,true),(3,true),(5,true)],
   [(1,true),(3,true),(4,true)],
   [(1,true),(4,true),(5,true)],
   [(1,true),(2,true),(3,true)]]

theorem gadget_shape :
    ∀ c ∈ gadget, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < 6 := by
  decide

theorem gadget_degree (i : ℕ) (hi : i < 6) :
    (gadget.flatMap (List.map Prod.fst)).count i = if i = 0 then 1 else 4 := by
  interval_cases i <;> decide

theorem gadget_accepts (a : Assignment) (h : ∀ i, 0 < i → i < 6 → a i = true) :
    CNF.eval a gadget = true := by
  have h1 := h 1 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide)
  have h3 := h 3 (by decide) (by decide)
  have h4 := h 4 (by decide) (by decide)
  have h5 := h 5 (by decide) (by decide)
  cases h0 : a 0 <;> simp [gadget,CNF.eval,Clause.eval,Literal.eval,h0,h1,h2,h3,h4,h5]

end PEqualNP.Outside.DegreeFill

open PEqualNP.Search

theorem PEqualNP.Outside.TernaryDegreeFillGadget :
    ∃ G : CNF,
      (∀ c ∈ G, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < 6) ∧
      (∀ i < 6, (G.flatMap (List.map Prod.fst)).count i = if i = 0 then 1 else 4) ∧
      (∀ a : Assignment, (∀ i, 0 < i → i < 6 → a i = true) → CNF.eval a G = true) := by
  open PEqualNP.Outside.DegreeFill in
  exact ⟨gadget,gadget_shape,gadget_degree,gadget_accepts⟩
