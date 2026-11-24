import PEqualNP.Outside.OneHotTableau

namespace PEqualNP.Outside.OneHot
open PEqualNP.Library.Universal PEqualNP.Search PEqualNP.Library.SearchHelpers.Tab

def Support (P : ℕ → Prop) (F : CNF) :=
  ∀ cl ∈ F, ∀ l ∈ cl, P l.1

theorem support_append {P : ℕ → Prop} {F G : CNF} :
    Support P (F ++ G) ↔ Support P F ∧ Support P G := by
  simp only [Support, List.mem_append, or_imp, forall_and]

theorem support_flatMap {α : Type} {l : List α} {f : α → CNF} {P : ℕ → Prop} :
    Support P (l.flatMap f) ↔ ∀ x ∈ l, Support P (f x) := by
  constructor
  · intro h x hx cl hc y hy
    exact h cl (List.mem_flatMap.mpr ⟨x, hx, hc⟩) y hy
  · intro h cl hc y hy
    obtain ⟨x, hx, hm⟩ := List.mem_flatMap.mp hc
    exact h x hx cl hm y hy

theorem support_map {α : Type} {l : List α} {f : α → Clause} {P : ℕ → Prop} :
    Support P (l.map f) ↔ ∀ x ∈ l, ∀ y ∈ f x, P y.1 := by
  simp only [Support, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h x hx
    exact h (f x) x hx rfl
  · rintro h _ x hx rfl
    exact h x hx

theorem imp_support {P : ℕ → Prop} {prem : List ℕ} {concl : ℕ}
    (hc : P concl) (hp : ∀ i ∈ prem, P i) :
    ∀ l ∈ imp prem concl, P l.1 := by
  intro l hl
  simp only [imp, List.mem_append, List.mem_map, List.mem_singleton] at hl
  rcases hl with ⟨i, hi, rfl⟩ | rfl
  · exact hp i hi
  · exact hc

def InGroups (K H B T x : ℕ) : Prop :=
  ∃ p ∈ groupVars K H B T, ∃ i < p.1, p.2 i = x

theorem in_pc {K H B T t q : ℕ} (ht : t ≤ T) (hq : q ≤ B) :
    InGroups K H B T (vP t q) := by
  refine ⟨(B+1,vP t), List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega), ?_⟩,
    q, by simp; omega, rfl⟩
  exact List.mem_append_left _ (by simp)

theorem in_state {K H B T t v : ℕ} (ht : t ≤ T) (hv : v < B) :
    InGroups K H B T (vQ t v) := by
  refine ⟨(B,vQ t), List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega), ?_⟩,
    v, hv, rfl⟩
  exact List.mem_append_left _ (by simp)

theorem in_cell {K H B T t k j x : ℕ} (ht : t ≤ T) (hk : k < K) (hj : j < H) (hx : x ≤ B) :
    InGroups K H B T (vC t k j x) := by
  refine ⟨(B+1,vC t k j), List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega), ?_⟩,
    x, by simp; omega, rfl⟩
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨k, List.mem_range.mpr hk, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩)

theorem newState_lt {i : Instr} {B v : ℕ} (h : Instr.bd i < B) (hv : v < B) (a : ℕ) :
    newState i v a < B := by
  cases i with
  | pop k tbl w next | peek k tbl w next =>
    have hb := Snd.getD_le_sum tbl (v*w+a)
    simp only [Instr.bd, newState] at *
    omega
  | load tbl next =>
    have hb := Snd.getD_le_sum tbl v
    simp only [Instr.bd, newState] at *
    omega
  | _ => exact hv

theorem read_support {K H B T t : ℕ} (ht : t ≤ T) (hH : 0 < H) (o : Option ℕ)
    (r : List ℕ × ℕ) (hr : r ∈ reads K B t o) :
    ∀ y ∈ r.1, InGroups K H B T y := by
  cases o with
  | none =>
    have he : r = ([],0) := by simpa [reads] using hr
    subst r
    simp
  | some k =>
    simp only [reads] at hr
    split at hr
    · rename_i hk
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      intro y hy
      simp only [List.mem_singleton] at hy
      subst y
      exact in_cell ht hk hH (by have := List.mem_range.mp hx; omega)
    · have he : r = ([], 0) := by simpa using hr
      subst r
      simp


theorem step_support {K H B T t : ℕ} {P : List Instr}
    (ht : t < T) (hH : 0 < H) (hB : 0 < B) (hP : ∀ i ∈ P, Instr.bd i < B) :
    Support (InGroups K H B T) (stepClauses K H B P t) := by
  have ht' : t+1 ≤ T := by omega
  have htl : t ≤ T := by omega
  unfold stepClauses
  rw [support_flatMap]
  intro q hq
  have hqb : q ≤ B := by have := List.mem_range.mp hq; omega
  let i := instrAt P q
  have hib : Instr.bd i < B := Snd.instrAt_bd hP hB q
  have hpc := in_pc (K := K) (H := H) htl hqb
  simp only [support_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pcClauses, support_map]
    intro v hv
    exact imp_support (in_pc ht' (Snd.nextCode_le hib v))
      (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hpc
        · exact in_state htl (List.mem_range.mp hv))
  · rw [stateClauses, support_flatMap]
    intro v hv
    rw [support_map]
    intro r hr
    apply imp_support (in_state ht' (newState_lt hib (List.mem_range.mp hv) r.2))
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact hpc
    · exact in_state htl (List.mem_range.mp hv)
    · exact read_support htl hH _ r hr y hy
  · rw [support_flatMap]
    intro k hk
    have hkb := List.mem_range.mp hk
    have cells (j l x : ℕ) (hj : j < H) (hl : l < H) (hx : x ≤ B) :
        ∀ y ∈ imp [vP t q, vC t k j x] (vC (t+1) k l x), InGroups K H B T y.1 :=
      imp_support (in_cell ht' hkb hl hx) (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hpc
        · exact in_cell htl hkb hj hx)
    change Support _ (cellClauses H B t q k (stackOp i k))
    cases ho : stackOp i k with
    | keep =>
      simp only [cellClauses, support_flatMap, support_map, List.mem_range]
      intro j hj x hx
      exact cells j j x hj hj (by omega)
    | push tbl =>
      simp only [cellClauses, support_append, support_flatMap, support_map, List.mem_range]
      constructor
      · intro v hv
        have hv' := Snd.getD_le_sum tbl v
        have hb := Snd.stackOp_push_bd ho
        apply imp_support (in_cell ht' hkb hH (by omega))
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hpc
        · exact in_state htl hv
      · intro j hj x hx
        exact cells j (j+1) x (by omega) (by omega) (by omega)
    | pop =>
      simp only [cellClauses, support_append, support_flatMap, support_map, List.mem_range]
      constructor
      · intro j hj x hx
        exact cells (j+1) j x (by omega) (by omega) (by omega)
      · intro cl hcl
        simp only [List.mem_singleton] at hcl
        subst cl
        exact imp_support (in_cell ht' hkb (by omega) (by omega)) (by
          intro y hy; simp only [List.mem_singleton] at hy; rwa [hy])


def Ghost (c : Code) (zs : List ℕ) (m H x : ℕ) : Prop :=
  c.kin < c.nstk ∧ ∃ j < H, x = vC 0 c.kin (zs.length + m + j) 0

theorem support_mono {P Q : ℕ → Prop} {F : CNF} (hF : Support P F)
    (h : ∀ x, P x → Q x) : Support Q F :=
  fun cl hc l hl => h l.1 (hF cl hc l hl)

theorem init_support (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4) :
    let H := cellsOf zs.length m T
    Support (fun x => InGroups c.nstk H (bound c) T x ∨ Ghost c zs m H x)
      (initClauses c zs m H) := by
  dsimp only
  let H := cellsOf zs.length m T
  let B := bound c
  let P := fun x => InGroups c.nstk H B T x ∨ Ghost c zs m H x
  have ht : 0 ≤ T := Nat.zero_le _
  have h4 : 4 ≤ B := by dsimp [B,bound]; omega
  change Support P (initClauses c zs m H)
  simp only [initClauses, support_append, support_flatMap, support_map, List.mem_range]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro cl hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have hpc : c.pc₀ + 1 ≤ B := by dsimp [B,bound]; omega
      exact imp_support (P := P) (Or.inl (in_pc ht hpc)) (by simp)
    · have hst : c.state₀ < B := by dsimp [B,bound]; omega
      exact imp_support (P := P) (Or.inl (in_state ht hst)) (by simp)
  · intro k hk
    split_ifs
    · intro cl hc
      simp at hc
    · rw [support_map]
      intro j hj
      exact imp_support (Or.inl (in_cell ht hk (List.mem_range.mp hj) (Nat.zero_le _))) (by simp)
  · split_ifs with hk
    · simp only [support_append, support_map, List.mem_range]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro j hj
        have hval : zs.getD j 0 < 4 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
          exact hz _ (List.getElem_mem hj)
        exact imp_support (Or.inl (in_cell ht hk (by dsimp [H, cellsOf]; omega)
          (by omega))) (by simp)
      · intro j hj l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;>
          exact Or.inl (in_cell ht hk (by dsimp [H,cellsOf]; omega) (by omega))
      · intro j hj
        apply imp_support (P := P) (Or.inl (in_cell ht hk (by dsimp [H,cellsOf]; omega) (Nat.zero_le _)))
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact Or.inl (in_cell ht hk (by dsimp [H,cellsOf]; omega) (Nat.zero_le _))
      · intro j hj
        exact imp_support (Or.inr ⟨hk,j,hj,rfl⟩) (by simp)
    · intro cl hc
      simp at hc


theorem final_support {K H B T : ℕ} (hH : 2 ≤ H) (c : Code) (hK : c.nstk = K) :
    Support (InGroups K H B T) (finalClauses c B T) := by
  simp only [finalClauses, support_append, support_map, List.mem_range]
  constructor
  · intro p hp y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact in_pc (Nat.le_refl _) (by omega)
  · split_ifs with hk
    · have hk' : c.kout < K := hK ▸ hk
      simp only [support_append, support_flatMap, support_map, List.mem_range]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro cl hc y hy
        simp only [List.mem_singleton] at hc hy
        subst cl
        simp only [List.mem_singleton] at hy
        subst y
        exact in_cell (Nat.le_refl _) hk' (by omega) (Nat.zero_le _)
      · intro x hx
        split_ifs
        · intro cl hc
          simp at hc
        · intro cl hc y hy
          simp only [List.mem_singleton] at hc
          subst cl
          simp only [List.mem_singleton] at hy
          subst y
          exact in_cell (Nat.le_refl _) hk' (by omega) (by omega)
      · intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst y
        exact in_cell (Nat.le_refl _) hk' (by omega) (by omega)
    · intro cl hc y hy
      simp only [List.mem_singleton] at hc
      subst cl
      simp at hy

theorem strengthening_support (K H B T : ℕ) :
    Support (InGroups K H B T) (strengthening K H B T) := by
  rw [strengthening, support_flatMap]
  intro ⟨n,f⟩ hp
  simp only [pairs, support_flatMap, support_map, List.mem_range]
  intro i hi j hj y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact ⟨(n,f), hp, i, hi, rfl⟩
  · exact ⟨(n,f), hp, j, Nat.lt_trans hj hi, rfl⟩

theorem formula_support (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4) :
    let H := cellsOf zs.length m T
    Support (fun x => InGroups c.nstk H (bound c) T x ∨ Ghost c zs m H x)
      (formula c zs m T) := by
  dsimp only
  let H := cellsOf zs.length m T
  have hH : 2 ≤ H := by dsimp [H,cellsOf]; omega
  have hB : 0 < bound c := by unfold bound; omega
  simp only [formula, tableau, support_append, support_flatMap]
  refine ⟨⟨⟨init_support c zs m T hz, ?_⟩, ?_⟩, ?_⟩
  · intro t ht
    exact support_mono (step_support (List.mem_range.mp ht) (by omega) hB (Snd.prog_bd c))
      (fun _ h => Or.inl h)
  · exact support_mono (final_support hH c rfl) (fun _ h => Or.inl h)
  · exact support_mono (strengthening_support c.nstk H (bound c) T) (fun _ h => Or.inl h)

end PEqualNP.Outside.OneHot
