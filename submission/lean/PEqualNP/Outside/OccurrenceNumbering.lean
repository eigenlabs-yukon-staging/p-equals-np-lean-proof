import PEqualNP.Outside.OccurrenceCycle

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Search

def number (j : ℕ) : Clause → Clause
  | [] => []
  | l :: ls => (j,l.2) :: number (j+1) ls

def main (j : ℕ) : CNF → CNF
  | [] => []
  | cl :: F => number j cl :: main (j+cl.length) F

theorem number_length (j : ℕ) (cl : Clause) : (number j cl).length = cl.length := by
  induction cl generalizing j with
  | nil => rfl
  | cons l ls ih => simp [number,ih]

theorem number_append (j : ℕ) (a b : Clause) :
    number j (a++b) = number j a ++ number (j+a.length) b := by
  induction a generalizing j with
  | nil => simp [number]
  | cons l a ih =>
    simp only [List.cons_append,number,List.length_cons,ih]
    rw [show j+1+a.length = j+(a.length+1) by omega]

theorem main_flatten (j : ℕ) (F : CNF) : (main j F).flatten = number j F.flatten := by
  induction F generalizing j with
  | nil => rfl
  | cons cl F ih =>
    simp [main,List.flatten_cons,ih,number_append]

theorem number_ids (j : ℕ) (cl : Clause) :
    (number j cl).map Prod.fst = (List.range cl.length).map (j+·) := by
  induction cl generalizing j with
  | nil => rfl
  | cons l ls ih =>
    rw [number,List.map_cons,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,ih]
    have he : (fun i => j + (i+1)) = (fun i => j+1+i) := funext fun i => by omega
    simpa only [Function.comp_def,Nat.add_zero,Nat.succ_eq_add_one,he]

theorem main_ids (F : CNF) : ids (main 0 F) = List.range F.flatten.length := by
  have he : ids (main 0 F) = (main 0 F).flatten.map Prod.fst := by
    simp [ids,List.flatMap_def,List.map_flatten]
  rw [he,main_flatten,number_ids]
  simp

def Agreement (σ τ : Assignment) (j : ℕ) (cl : Clause) :=
  ∀ i : ℕ, i < cl.length → σ (j+i) = τ ((cl[i]?).getD (0,false)).1

theorem eval_number (σ τ : Assignment) (j : ℕ) (cl : Clause)
    (h : Agreement σ τ j cl) :
    Clause.eval σ (number j cl) = Clause.eval τ cl := by
  induction cl generalizing j with
  | nil => rfl
  | cons l ls ih =>
    have h0 : σ j = τ l.1 := by
      simpa using h 0 (by simp)
    have htail : Agreement σ τ (j+1) ls := by
      intro i hi
      simpa [List.getElem?_cons_succ,show j+1+i=j+(i+1) by omega] using
        h (i+1) (by simp; omega)
    change (Literal.eval σ (j,l.2) || Clause.eval σ (number (j+1) ls)) =
      (Literal.eval τ l || Clause.eval τ ls)
    rw [ih (j+1) htail]
    simp [Literal.eval,h0]

theorem eval_main (σ τ : Assignment) (j : ℕ) (F : CNF)
    (h : Agreement σ τ j F.flatten) :
    CNF.eval σ (main j F) = CNF.eval τ F := by
  induction F generalizing j with
  | nil => rfl
  | cons cl F ih =>
    have h1 : Agreement σ τ j cl := by
      intro i hi
      have h' := h i (by simp; omega)
      simpa only [List.flatten_cons,List.getElem?_append_left hi] using h'
    have h2 : Agreement σ τ (j+cl.length) F.flatten := by
      intro i hi
      have h' := h (cl.length+i) (by
        simp only [List.flatten_cons,List.length_append]
        exact Nat.add_lt_add_left hi _)
      simpa [List.getElem?_append_right, Nat.add_assoc] using h'
    change (Clause.eval σ (number j cl) && CNF.eval σ (main (j+cl.length) F)) =
      (Clause.eval τ cl && CNF.eval τ F)
    rw [eval_number _ _ _ _ h1,ih _ h2]

theorem main_width (k j : ℕ) (F : CNF) (h : IsKCNF k F) : IsKCNF k (main j F) := by
  induction F generalizing j with
  | nil => exact h
  | cons cl F ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | htail
    · simpa only [number_length] using h cl (List.mem_cons_self ..)
    · exact ih (j+cl.length) (fun c hc => h c (List.mem_cons_of_mem _ hc)) c htail

end PEqualNP.Outside.OccurrenceSplit
