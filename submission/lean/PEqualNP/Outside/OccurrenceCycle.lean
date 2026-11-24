import PEqualNP.Defs

namespace PEqualNP.Outside.OccurrenceSplit
open PEqualNP.Search

def arc (a b : ℕ) : Clause := [(a,false),(b,true)]

def chain (first cur : ℕ) : List ℕ → CNF
  | [] => [arc cur first]
  | n :: ns => arc cur n :: chain first n ns

def cycle : List ℕ → CNF
  | [] => []
  | a :: as => chain a a as

def ids (F : CNF) : List ℕ := F.flatMap (List.map Prod.fst)

theorem ids_append (F G : CNF) : ids (F++G) = ids F ++ ids G :=
  List.flatMap_append ..

theorem arc_eval (σ : Assignment) (a b : ℕ) :
    Clause.eval σ (arc a b) = true ↔ (σ a = true → σ b = true) := by
  cases ha : σ a <;> cases hb : σ b <;>
    simp [arc,Clause.eval,Literal.eval,ha,hb]

theorem chain_sound (σ : Assignment) (first cur : ℕ) (ns : List ℕ)
    (h : CNF.eval σ (chain first cur ns) = true) :
    (∀ n ∈ cur::ns, σ n = true → σ first = true) ∧
      (σ cur = true → ∀ n ∈ cur::ns, σ n = true) := by
  induction ns generalizing cur with
  | nil =>
    have h0 : Clause.eval σ (arc cur first) = true := by simpa [chain,CNF.eval] using h
    exact ⟨by simpa using (arc_eval σ cur first).mp h0, by simp⟩
  | cons n ns ih =>
    have hs : Clause.eval σ (arc cur n) = true ∧ CNF.eval σ (chain first n ns) = true := by
      simpa only [chain,CNF.eval,List.all_cons,Bool.and_eq_true_iff] using h
    have hi := ih n hs.2
    have hb := (arc_eval σ cur n).mp hs.1
    constructor
    · intro x hx htrue
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hi.1 n (List.mem_cons_self ..) (hb htrue)
      · exact hi.1 x hx htrue
    · intro htrue x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact htrue
      · exact hi.2 (hb htrue) x hx

theorem chain_complete (σ : Assignment) (first cur : ℕ) (ns : List ℕ)
    (h : ∀ n ∈ cur::ns, σ n = σ first) : CNF.eval σ (chain first cur ns) = true := by
  induction ns generalizing cur with
  | nil =>
    have hf := h cur (List.mem_cons_self ..)
    have he := (arc_eval σ cur first).mpr (fun hin => hf.symm.trans hin)
    simpa [CNF.eval,chain] using he
  | cons n ns ih =>
    have hq := ih n (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have he := (arc_eval σ cur n).mpr (fun hc =>
      (h n (by simp)).trans ((h cur (by simp)).symm.trans hc))
    simpa only [CNF.eval,chain,List.all_cons,Bool.and_eq_true_iff] using And.intro he hq

theorem cycle_eval (σ : Assignment) (ns : List ℕ) :
    CNF.eval σ (cycle ns) = true ↔ ∀ a ∈ ns, ∀ b ∈ ns, σ a = σ b := by
  cases ns with
  | nil => simp [cycle,CNF.eval]
  | cons x xs =>
    constructor
    · intro h
      have G := chain_sound σ x x xs h
      have eq (a : ℕ) (ha : a ∈ x::xs) : σ a = σ x := by
        cases h₁ : σ a <;> cases h₂ : σ x
        · rfl
        · exact False.elim (Bool.noConfusion (h₁.symm.trans (G.2 h₂ a ha)))
        · exact False.elim (Bool.noConfusion (h₂.symm.trans (G.1 a ha h₁)))
        · rfl
      exact fun a ha b hb => (eq a ha).trans (eq b hb).symm
    · intro h
      exact chain_complete σ x x xs (fun a ha => h a ha x (List.mem_cons_self ..))

theorem chain_count (first cur x : ℕ) (ns : List ℕ) :
    (ids (chain first cur ns)).count x =
      (if cur = x then 1 else 0) + (if first = x then 1 else 0) + 2*ns.count x := by
  induction ns generalizing cur with
  | nil =>
    by_cases h₁ : cur = x <;> by_cases h₂ : first = x <;>
      simp [chain,ids,arc,List.count_cons,h₁,h₂,eq_comm]
  | cons n ns ih =>
    change (cur::n::ids (chain first n ns)).count x = _
    simp only [List.count_cons,ih,beq_iff_eq]
    by_cases h₁ : cur = x <;> by_cases h₂ : n = x <;> by_cases h₃ : first = x <;>
      simp [h₁,h₂,h₃,eq_comm] <;> omega

theorem cycle_count (ns : List ℕ) (x : ℕ) :
    (ids (cycle ns)).count x = 2*ns.count x := by
  cases ns with
  | nil => simp [cycle,ids]
  | cons a as =>
    rw [cycle,chain_count]
    by_cases h : a = x <;> simp [List.count_cons,h,eq_comm] <;> omega

end PEqualNP.Outside.OccurrenceSplit
