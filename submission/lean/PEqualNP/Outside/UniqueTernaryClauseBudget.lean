import PEqualNP.Outside.UniqueTernaryBlockerStructure

namespace PEqualNP.Outside.UniqueTernaryBlocker
open PEqualNP.Search
open PEqualNP.Outside.ZeroClauseBlockers (assign)

theorem negative_exists (c : Clause) (h : Clause.eval (fun _ => false) c = true) :
    ∃ v, (v,false) ∈ c := by
  obtain ⟨⟨v,b⟩,hv,he⟩ := List.any_eq_true.mp h
  cases b
  · exact ⟨v,hv⟩
  · simp [Literal.eval] at he

theorem all_negative_mem (c : Clause) (h : ∀ l ∈ c, l.2 = false) (v : ℕ)
    (hv : v ∈ c.map Prod.fst) : (v,false) ∈ c := by
  obtain ⟨⟨i,b⟩,hi,rfl⟩ := List.mem_map.mp hv
  have hb : b = false := h _ hi
  simpa [hb] using hi

def avoiding {n : ℕ} (O : Finset ℕ) : Fin n → Bool := fun i => decide (i.1 ∉ O)

theorem literal_true (n : ℕ) (O : Finset ℕ) (v : ℕ) (hv : v < n) (p : Bool)
    (hp : decide (v ∉ O) = p) : Literal.eval (assign (avoiding (n := n) O)) (v,p) = true := by
  simp [Literal.eval,assign,avoiding,hv,hp]

theorem omitted_hits (n : ℕ) (O : Finset ℕ) (c : Clause)
    (hRange : ∀ l ∈ c, l.1 < n) (v : ℕ) (hv : v ∈ O) (hmem : (v,false) ∈ c) :
    Clause.eval (assign (avoiding (n := n) O)) c = true :=
  List.any_eq_true.mpr ⟨(v,false),hmem,literal_true n O v (hRange _ hmem) false (by simp [hv])⟩

theorem selected_hits (n : ℕ) (O : Finset ℕ) (c : Clause)
    (hRange : ∀ l ∈ c, l.1 < n)
    (hForm : ∃ i a b : ℕ, a ≠ b ∧ c.Perm [(i,false),(a,true),(b,true)])
    (hO : ∀ a b : ℕ, a ≠ b → (a,true) ∈ c → (b,true) ∈ c → ¬ (a ∈ O ∧ b ∈ O)) :
    Clause.eval (assign (avoiding (n := n) O)) c = true := by
  obtain ⟨i,a,b,hn,hp⟩ := hForm
  have hA : (a,true) ∈ c := hp.mem_iff.mpr (by simp)
  have hB : (b,true) ∈ c := hp.mem_iff.mpr (by simp)
  by_cases ha : a ∈ O
  · have hb : b ∉ O := fun h => hO a b hn hA hB ⟨ha,h⟩
    exact List.any_eq_true.mpr ⟨(b,true),hB,literal_true n O b (hRange _ hB) true (by simp [hb])⟩
  · exact List.any_eq_true.mpr ⟨(a,true),hA,literal_true n O a (hRange _ hA) true (by simp [ha])⟩

theorem budget (n : ℕ) (F : CNF) (hn : 3 ≤ n)
    (hS : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n)
    (hD : ∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 4)
    (hZero : CNF.eval (fun _ => false) F = true)
    (hUnique : ∀ b : Fin n → Bool, CNF.eval (assign b) F = true → ∀ j, b j = false) :
    n+3 ≤ F.length := by
  classical
  by_contra hSize
  have hFew : F.length ≤ n+2 := by omega
  obtain ⟨hBlocks,E,hEF,hAll⟩ := PEqualNP.Outside.UniqueZeroClauseBlockers F n (by omega)
    (fun c hc => (hS c hc).2.2) hZero hUnique
  have hChoose (i : Fin n) : ∃ c ∈ F, blocker i.1 c := hBlocks i.1 i.2
  choose c hCF hBlock using hChoose
  have hInj : Function.Injective c := by
    intro i j h
    apply Fin.ext
    exact blocker_inj (hBlock i) (h.symm ▸ hBlock j)
  let B := (Finset.univ : Finset (Fin n)).image c
  have hCardB : B.card = n := by simp [B,Finset.card_image_of_injective _ hInj]
  have hB (C : Clause) (hC : C ∈ B) : C ∈ F := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hC
    exact hCF i
  have hE : E ∉ B := by
    intro hEB
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hEB
    have hES := hS E hEF
    exact all_negative_not_blocker i.1 E hES.1 hES.2.1 hAll (he ▸ hBlock i)
  have hForm (C : Clause) (hCB : C ∈ B) :
      ∃ i a b : ℕ, a ≠ b ∧ C.Perm [(i,false),(a,true),(b,true)] := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hCB
    obtain ⟨a,b,_,_,hne,hP⟩ := form i.1 (c i) (hBlock i) (hS _ (hCF i)).1 (hS _ (hCF i)).2.1
    exact ⟨i.1,a,b,hne,hP⟩
  let T := F.toFinset \ insert E B
  have hSub : insert E B ⊆ F.toFinset := by
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact List.mem_toFinset.mpr hEF
    · exact List.mem_toFinset.mpr (hB C hC)
  have hT : T.card ≤ 1 := by
    unfold T
    rw [Finset.card_sdiff_of_subset hSub,Finset.card_insert_of_notMem hE,hCardB]
    have hh := List.toFinset_card_le F
    omega
  have hES := hS E hEF
  have hEN : ∃ e, (e,false) ∈ E :=
    negative_exists E (List.all_eq_true.mp hZero E hEF)
  obtain ⟨e0,he0⟩ := hEN
  have hO : ∃ O : Finset ℕ, O.card ≤ 2 ∧
      (∀ C ∈ B, ∀ a b : ℕ, a ≠ b → (a,true) ∈ C → (b,true) ∈ C → ¬ (a ∈ O ∧ b ∈ O)) ∧
      (∀ C ∈ F, C ∉ B → ∃ v ∈ O, (v,false) ∈ C) := by
    by_cases hEmpty : T = ∅
    · refine ⟨{e0},by simp,?_,?_⟩
      · intro C hC a b ha _ _ h
        simp only [Finset.mem_singleton] at h
        exact ha (h.1.trans h.2.symm)
      · intro C hC hCB
        by_cases he : C = E
        · exact ⟨e0,by simp,he.symm ▸ he0⟩
        · have hh : C ∈ T := Finset.mem_sdiff.mpr
            ⟨List.mem_toFinset.mpr hC,fun hm => (Finset.mem_insert.mp hm).elim he hCB⟩
          simp [hEmpty] at hh
    · have hOne : T.card = 1 := by
        have hh := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
        omega
      obtain ⟨C,hC⟩ := Finset.card_eq_one.mp hOne
      have hCT : C ∈ T := by simp [hC]
      have hCF' : C ∈ F := List.mem_toFinset.mp (Finset.mem_sdiff.mp hCT).1
      have hNot : C ∉ insert E B := (Finset.mem_sdiff.mp hCT).2
      obtain ⟨v,hvN⟩ := negative_exists C (List.all_eq_true.mp hZero C hCF')
      have hOther : ∀ D ∈ F, D ∉ B → D = E ∨ D = C := by
        intro D hDF hDB
        by_cases he : D = E
        · exact Or.inl he
        · have hh : D ∈ T := Finset.mem_sdiff.mpr
            ⟨List.mem_toFinset.mpr hDF,fun hmem => (Finset.mem_insert.mp hmem).elim he hDB⟩
          exact Or.inr (by simpa [hC] using hh)
      by_cases hvE : v ∈ E.map Prod.fst
      · refine ⟨{v},by simp,?_,?_⟩
        · intro D hD a b ha _ _ h
          simp only [Finset.mem_singleton] at h
          exact ha (h.1.trans h.2.symm)
        · intro D hDF hDB
          rcases hOther D hDF hDB with he | he
          · subst D
            exact ⟨v,by simp,all_negative_mem E hAll v hvE⟩
          · subst D
            exact ⟨v,by simp,hvN⟩
      · have hvR : v < n := (hS C hCF').2.2 _ hvN
        let v' : Fin n := ⟨v,hvR⟩
        have hCB : c v' ∈ B := Finset.mem_image.mpr ⟨v',Finset.mem_univ _,rfl⟩
        have hcNe : c v' ≠ C := fun h => hNot (Finset.mem_insert_of_mem (h ▸ hCB))
        have hCap := two_negative_cap F v (c v') C (hCF v') hCF' hcNe (hBlock v').1 hvN (hD v)
        obtain ⟨e,he,hHole⟩ := exists_hole F B E v ⟨hES.1,hES.2.1⟩ hvE hB
          (fun D hD => by obtain ⟨i,a,b,_,h⟩ := hForm D hD; exact ⟨i,a,b,h⟩) hCap
        refine ⟨{v,e},by by_cases h : v = e <;> simp [h],?_,?_⟩
        · intro D hDB a b hNe hA hB' hBoth
          simp only [Finset.mem_insert,Finset.mem_singleton] at hBoth
          rcases hBoth with ⟨rfl | rfl,rfl | rfl⟩
          · exact hNe rfl
          · exact hHole D hDB ⟨hA,hB'⟩
          · exact hHole D hDB ⟨hB',hA⟩
          · exact hNe rfl
        · intro D hDF hDB
          rcases hOther D hDF hDB with hEq | hEq
          · subst D
            exact ⟨e,by simp,all_negative_mem E hAll e he⟩
          · subst D
            exact ⟨v,by simp,hvN⟩
  obtain ⟨O,hOC,hGood,hExtra⟩ := hO
  have hSat : CNF.eval (assign (avoiding (n := n) O)) F = true := by
    apply List.all_eq_true.mpr
    intro C hC
    by_cases hCB : C ∈ B
    · exact selected_hits n O C (hS C hC).2.2 (hForm C hCB) (hGood C hCB)
    · obtain ⟨v,hv,hMem⟩ := hExtra C hC hCB
      exact omitted_hits n O C (hS C hC).2.2 v hv hMem
  have hUnused : ∃ i : Fin n, i.1 ∉ O := by
    by_contra h
    push Not at h
    have hSub : Finset.range n ⊆ O := fun i hi => h ⟨i,Finset.mem_range.mp hi⟩
    have hh := Finset.card_le_card hSub
    simp only [Finset.card_range] at hh
    omega
  obtain ⟨i,hi⟩ := hUnused
  have hh := hUnique _ hSat i
  simp [avoiding,hi] at hh

end PEqualNP.Outside.UniqueTernaryBlocker

open PEqualNP.Search

theorem PEqualNP.Outside.UniqueTernaryClauseBudget :
    ∀ (n : ℕ) (F : CNF), 3 ≤ n →
      (∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) →
      (∀ v, (F.flatMap (List.map Prod.fst)).count v ≤ 4) →
      CNF.eval (fun _ => false) F = true →
      (∀ a : Fin n → Bool,
        CNF.eval (fun i => if h : i < n then a ⟨i,h⟩ else false) F = true → ∀ j, a j = false) →
      n+3 ≤ F.length := by
  exact PEqualNP.Outside.UniqueTernaryBlocker.budget
