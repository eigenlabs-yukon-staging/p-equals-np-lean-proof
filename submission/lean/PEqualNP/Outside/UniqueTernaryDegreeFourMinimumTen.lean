import PEqualNP.Outside.UniqueTernaryClauseBudget
import PEqualNP.Outside.UniqueTernaryDegreeFourMinimumNames

namespace PEqualNP.Outside.UniqueTernaryBlocker
open PEqualNP.Search
open PEqualNP.Outside.ZeroClauseBlockers (assign)
open PEqualNP.Outside.UniqueTernaryCount (degree_sum)

def twist (a : Assignment) (l : Literal) : Literal :=
  (l.1,if a l.1 then !l.2 else l.2)

def twistFormula (a : Assignment) (F : CNF) : CNF := F.map (List.map (twist a))

def twistAssignment (a b : Assignment) : Assignment :=
  fun i => if a i then !b i else b i

theorem twist_lit (a b : Assignment) (l : Literal) :
    Literal.eval b (twist a l) = Literal.eval (twistAssignment a b) l := by
  obtain ⟨i,p⟩ := l
  cases ha : a i <;> cases hb : b i <;> cases p <;>
    simp [Literal.eval,twist,twistAssignment,ha,hb]

theorem twist_eval (a b : Assignment) (F : CNF) :
    CNF.eval b (twistFormula a F) = CNF.eval (twistAssignment a b) F := by
  simp [CNF.eval,Clause.eval,twistFormula,List.all_map,List.any_map,Function.comp_def,twist_lit]
  rfl

theorem twist_names (a : Assignment) (F : CNF) :
    (twistFormula a F).flatMap (List.map Prod.fst) = F.flatMap (List.map Prod.fst) := by
  simp [twistFormula,List.flatMap_map,List.map_map,Function.comp_def,twist]

theorem twist_shape (n : ℕ) (a : Assignment) (F : CNF)
    (h : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) :
    ∀ c ∈ twistFormula a F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n := by
  intro c hc
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hc
  obtain ⟨hL,hN,hR⟩ := h u hu
  simp only [List.length_map,List.map_map,Function.comp_def,twist]
  refine ⟨hL,hN,?_⟩
  intro l hl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hl
  exact hR w hw

theorem twist_fin {n : ℕ} (a b : Fin n → Bool) :
    twistAssignment (assign a) (assign b) =
      assign (fun i => if a i then !b i else b i) := by
  funext i
  by_cases h : i < n <;> simp [assign,twistAssignment,h]

theorem width_requires_names (F : CNF) (n : ℕ) (terminal : ℕ) (ht : terminal < n)
    (hS : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n)
    (hu : ∃! a : Fin n → Bool, CNF.eval (assign a) F = true) : 3 ≤ n := by
  cases F with
  | nil =>
    obtain ⟨a,_,h⟩ := hu
    let i : Fin n := ⟨terminal,ht⟩
    let b : Fin n → Bool := fun _ => !a i
    have he := congrFun (h b rfl) i
    change (!a i) = a i at he
    cases ha : a i <;> simp [ha] at he
  | cons c F =>
    obtain ⟨hL,hN,hR⟩ := hS c (List.mem_cons_self ..)
    have hSub : (c.map Prod.fst).toFinset ⊆ Finset.range n := by
      intro v hv
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact Finset.mem_range.mpr (hR _ hl)
    have hCard := Finset.card_le_card hSub
    simpa [List.toFinset_card_of_nodup hN,hL] using hCard

theorem minimum_ten (n : ℕ) (F : CNF) (terminal : ℕ)
    (ht : terminal < n)
    (hS : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n)
    (hD : ∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 4)
    (hT : (F.flatMap (List.map Prod.fst)).count terminal ≤ 3)
    (hu : ∃! a : Fin n → Bool, CNF.eval (assign a) F = true) : 10 ≤ n := by
  have hn := width_requires_names F n terminal ht hS hu
  obtain ⟨a,ha,hUnique⟩ := hu
  let G := twistFormula (assign a) F
  have hG := twist_shape n (assign a) F hS
  have hName := twist_names (assign a) F
  have hZD : twistAssignment (assign a) (fun _ => false) = assign a := by
    funext i
    cases h : assign a i <;> simp [twistAssignment,h]
  have hZero : CNF.eval (fun _ => false) G = true := by
    change CNF.eval (fun _ => false) (twistFormula (assign a) F) = true
    rw [twist_eval,hZD]
    exact ha
  have hU : ∀ b : Fin n → Bool, CNF.eval (assign b) G = true → ∀ i, b i = false := by
    intro b hb i
    change CNF.eval (assign b) (twistFormula (assign a) F) = true at hb
    rw [twist_eval,twist_fin] at hb
    have he := congrFun (hUnique _ hb) i
    cases ha' : a i <;> cases hb' : b i <;> simp_all
  have hBy := budget n G hn hG (fun v => hName.symm ▸ hD v) hZero hU
  have hSum := degree_sum F n terminal ht (fun c hc => ⟨(hS c hc).1,(hS c hc).2.2⟩) hD hT
  have hLen : G.length = F.length := by simp [G,twistFormula]
  omega

end PEqualNP.Outside.UniqueTernaryBlocker

open PEqualNP.Search

theorem PEqualNP.Outside.UniqueTernaryDegreeFourMinimumTen :
    ∀ (n : ℕ) (F : CNF) (terminal : ℕ), terminal < n →
      (∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) →
      (∀ i, (F.flatMap (List.map Prod.fst)).count i ≤ 4) →
      (F.flatMap (List.map Prod.fst)).count terminal ≤ 3 →
      (∃! a : Fin n → Bool,
        CNF.eval (fun i => if h : i < n then a ⟨i,h⟩ else false) F = true) →
      10 ≤ n := by
  exact PEqualNP.Outside.UniqueTernaryBlocker.minimum_ten
