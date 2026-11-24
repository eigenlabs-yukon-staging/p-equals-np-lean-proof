import PEqualNP.Library.SearchHelpers.TableauSound
import PEqualNP.Library.SearchHelpers.TableauComplete

namespace PEqualNP.Outside.OneHot
open PEqualNP.Library.Universal PEqualNP.Search PEqualNP.Library.SearchHelpers.Tab

def pairs (n : ℕ) (f : ℕ → ℕ) : CNF :=
  (List.range n).flatMap fun i =>
    (List.range i).map fun j => [(f i, false), (f j, false)]

theorem pairs_iff (σ : Assignment) (n : ℕ) (f : ℕ → ℕ) :
    CNF.eval σ (pairs n f) = true ↔
      ∀ i < n, ∀ j < n, σ (f i) = true → σ (f j) = true → i = j := by
  have eval (i j : ℕ) :
      Clause.eval σ [(f i, false), (f j, false)] = true ↔
        ¬ (σ (f i) = true ∧ σ (f j) = true) := by
    cases hi : σ (f i) <;> cases hj : σ (f j) <;>
      simp [Clause.eval, Literal.eval, hi, hj]
  constructor
  · intro h i hi j hj hsi hsj
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact False.elim ((eval j i).mp (Snd.eval_all h
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
          List.mem_map.mpr ⟨i, List.mem_range.mpr hij, rfl⟩⟩)) ⟨hsj, hsi⟩)
    · rfl
    · exact False.elim ((eval i j).mp (Snd.eval_all h
        (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
          List.mem_map.mpr ⟨j, List.mem_range.mpr hij, rfl⟩⟩)) ⟨hsi, hsj⟩)
  · intro h
    unfold CNF.eval
    rw [List.all_eq_true]
    intro cl hc
    obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
    have hij := List.mem_range.mp hj
    exact (eval i j).mpr fun ⟨hsi, hsj⟩ =>
      (Nat.ne_of_gt hij) (h i (List.mem_range.mp hi) j
        (lt_trans hij (List.mem_range.mp hi)) hsi hsj)

def groupVars (K H B T : ℕ) : List (ℕ × (ℕ → ℕ)) :=
  (List.range (T + 1)).flatMap fun t =>
    [(B + 1, vP t), (B, vQ t)] ++
      (List.range K).flatMap fun k =>
        (List.range H).map fun j => (B + 1, vC t k j)

def strengthening (K H B T : ℕ) : CNF :=
  (groupVars K H B T).flatMap fun (n, f) => pairs n f

theorem strengthening_iff (σ : Assignment) (K H B T : ℕ) :
    CNF.eval σ (strengthening K H B T) = true ↔
      ∀ p ∈ groupVars K H B T,
        ∀ i < p.1, ∀ j < p.1, σ (p.2 i) = true → σ (p.2 j) = true → i = j := by
  simp only [strengthening, CNF.eval, List.all_eq_true, List.mem_flatMap]
  constructor
  · intro h ⟨n, f⟩ hp
    apply (pairs_iff σ n f).mp
    exact List.all_eq_true.mpr fun cl hc => h cl ⟨(n, f), hp, hc⟩
  · intro h cl ⟨⟨n, f⟩, hp, hc⟩
    exact Snd.eval_all ((pairs_iff σ n f).mpr (h (n, f) hp)) hc


def formula (c : Code) (zs : List ℕ) (m T : ℕ) : CNF :=
  tableau c zs m T ++ strengthening c.nstk (cellsOf zs.length m T) (bound c) T

def inputOf (zs : List ℕ) (w : List Bool) := zs ++ w.map (fun b => cond b 3 2)

def Agrees (c : Code) (zs : List ℕ) (m T : ℕ) (w : List Bool)
    (σ : Assignment) : Prop :=
  ∀ p ∈ groupVars c.nstk (cellsOf zs.length m T) (bound c) T,
    ∀ i < p.1, σ (p.2 i) = Cpl.asg c (inputOf zs w) (p.2 i)

theorem canonical_model (c : Code) (zs : List ℕ) (m T : ℕ) (w : List Bool)
    (hw : w.length ≤ m) (h : c.outputsWithin (inputOf zs w) T [1]) :
    CNF.eval (Cpl.asg c (inputOf zs w)) (formula c zs m T) = true := by
  let σ := Cpl.asg c (inputOf zs w)
  have base : CNF.eval σ (tableau c zs m T) = true := by
    unfold CNF.eval tableau
    rw [List.all_eq_true]
    intro cl hcl
    simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hcl
    rcases hcl with (hcl | ⟨t, ht, hcl⟩) | hcl
    · exact Cpl.init_ok c zs w m _ hw cl hcl
    · refine Cpl.step_ok c _ t _ _ ?_ cl hcl
      have hl : (inputOf zs w).length = zs.length + w.length := by simp [inputOf]
      rw [hl]
      unfold cellsOf
      omega
    · exact Cpl.final_ok c _ _ T h cl hcl
  have extra : CNF.eval σ (strengthening c.nstk (cellsOf zs.length m T) (bound c) T) = true := by
    apply (strengthening_iff ..).mpr
    intro ⟨n, f⟩ hp i _ j _ hi hj
    simp only [groupVars, List.mem_flatMap, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range, Prod.mk.injEq] at hp
    obtain ⟨t, _, hp⟩ := hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨k, _, l, _, rfl, rfl⟩
    · exact ((Cpl.asg_vP ..).mp hi).trans ((Cpl.asg_vP ..).mp hj).symm
    · exact ((Cpl.asg_vQ ..).mp hi).trans ((Cpl.asg_vQ ..).mp hj).symm
    · exact ((Cpl.asg_vC ..).mp hi).trans ((Cpl.asg_vC ..).mp hj).symm
  change CNF.eval σ (formula c zs m T) = true
  simpa only [formula, CNF.eval, List.all_append, Bool.and_eq_true_iff] using
    (show _ ∧ _ from ⟨base, extra⟩)


theorem complete_group {σ τ : Assignment} {n a : ℕ} {f : ℕ → ℕ}
    (unique : ∀ i < n, ∀ j < n, σ (f i) = true → σ (f j) = true → i = j)
    (ha : a < n) (hsa : σ (f a) = true)
    (canon : ∀ i, τ (f i) = true ↔ i = a) :
    ∀ i < n, σ (f i) = τ (f i) := by
  intro i hi
  have equiv : σ (f i) = true ↔ τ (f i) = true := by
    rw [canon]
    exact ⟨fun h => unique i hi a ha h hsa, fun h => h ▸ hsa⟩
  cases hσ : σ (f i) <;> cases hτ : τ (f i) <;> simp_all

theorem decode (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4)
    (σ : Assignment) (hσ : CNF.eval σ (formula c zs m T) = true) :
    ∃ w : List Bool, w.length ≤ m ∧ c.outputsWithin (inputOf zs w) T [1] ∧
      Agrees c zs m T w σ := by
  let H := cellsOf zs.length m T
  let B := bound c
  have hsplit : CNF.eval σ (tableau c zs m T) = true ∧
      CNF.eval σ (strengthening c.nstk H B T) = true := by
    simpa only [formula, CNF.eval, List.all_append, Bool.and_eq_true_iff] using hσ
  obtain ⟨hb, he⟩ := hsplit
  have hall : ∀ cl ∈ tableau c zs m T, Clause.eval σ cl = true :=
    fun cl hcl => Snd.eval_all hb hcl
  have hinit : ∀ cl ∈ initClauses c zs m H, Clause.eval σ cl = true :=
    fun cl hcl => hall cl (List.mem_append_left _ (List.mem_append_left _ hcl))
  have hstep : ∀ t < T, ∀ cl ∈ stepClauses c.nstk H B c.prog t, Clause.eval σ cl = true :=
    fun t ht cl hcl => hall cl (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, hcl⟩)))
  have hfin : ∀ cl ∈ finalClauses c B T, Clause.eval σ cl = true :=
    fun cl hcl => hall cl (List.mem_append_right _ hcl)
  obtain ⟨w, hw, hwit⟩ := Snd.wit c zs m H hinit
  have hrun : ∀ t ≤ T, Snd.Inv σ c.nstk H B
      (zs.length + m + t) t (c.run (inputOf zs w) t) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact Snd.init_inv c zs m H w hz hw hinit hwit
    | succ t ih =>
      intro ht
      have hlt : zs.length + m + t < H := by
        change zs.length + m + t < zs.length + m + T + 2
        omega
      rw [Code.run, Function.iterate_succ_apply']
      exact Snd.step_inv (ih (by omega)) hlt (Snd.prog_bd c) (hstep t (by omega))
  refine ⟨w, hw, Snd.final_out (hrun T (Nat.le_refl _)) ?_ hfin, ?_⟩
  · change 2 ≤ zs.length + m + T + 2
    omega
  · unfold Agrees
    intro ⟨n, f⟩ hp
    have hu := (strengthening_iff ..).mp he (n, f) hp
    simp only [groupVars, List.mem_flatMap, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range, Prod.mk.injEq] at hp
    obtain ⟨t, ht, hp⟩ := hp
    have inv := hrun t (by omega)
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨k, hk, j, hj, rfl, rfl⟩
    · exact complete_group hu (Nat.lt_succ_of_le inv.pcB) inv.pc (fun i => Cpl.asg_vP ..)
    · exact complete_group hu inv.stB inv.st (fun i => Cpl.asg_vQ ..)
    · exact complete_group hu (Nat.lt_succ_of_le (Snd.cellVal_le (inv.symB k hk) j))
        (inv.cell k hk j hj) (fun i => by
          rw [Cpl.asg_vC]
          simp only [Cpl.cellOf, Snd.cellVal]
          cases ((c.run (inputOf zs w) t).stk.getD k [])[j]? <;> rfl)


theorem unique_witness {c : Code} {zs : List ℕ} {m T : ℕ} {u w : List Bool} {σ : Assignment}
    (hk : c.kin < c.nstk) (hu : u.length ≤ m) (hw : w.length ≤ m)
    (hU : Agrees c zs m T u σ) (hW : Agrees c zs m T w σ) : u = w := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < m
  · let l := zs.length + j
    let a := Cpl.cellOf (u.map fun b => cond b 3 2) j
    have ht : 0 ∈ List.range (T + 1) := List.mem_range.mpr (by omega)
    have hcell : l ∈ List.range (cellsOf zs.length m T) := List.mem_range.mpr (by
      change zs.length + j < zs.length + m + T + 2
      omega)
    have hp : (bound c + 1, vC 0 c.kin l) ∈
        groupVars c.nstk (cellsOf zs.length m T) (bound c) T := by
      apply List.mem_flatMap.mpr
      exact ⟨0, ht, List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨c.kin, List.mem_range.mpr hk, List.mem_map.mpr ⟨l, hcell, rfl⟩⟩)⟩
    have ha : a < bound c + 1 := by
      have hv := Cpl.cellOf_witness u j
      change _ < c.pc₀ + c.state₀ + (c.prog.map Instr.bd).sum + 4 + 1
      rcases hv with h | h | h <;> dsimp [a] <;> omega
    have heq := (hU _ hp a ha).symm.trans (hW _ hp a ha)
    change Cpl.asg c (inputOf zs u) (vC 0 c.kin l a) =
      Cpl.asg c (inputOf zs w) (vC 0 c.kin l a) at heq
    have code (r : List Bool) : Cpl.asg c (inputOf zs r) (vC 0 c.kin l a) = true ↔
        a = Cpl.cellOf (r.map fun b => cond b 3 2) j := by
      rw [Cpl.asg_vC, Cpl.stk_init, if_pos ⟨rfl, hk⟩]
      exact iff_of_eq (congrArg (fun x => a = x) (Cpl.cellOf_append_right ..))
    have hval : Cpl.cellOf (u.map fun b => cond b 3 2) j =
        Cpl.cellOf (w.map fun b => cond b 3 2) j :=
      (code w).mp (heq ▸ (code u).mpr rfl)
    simp only [Cpl.cellOf, List.getElem?_map] at hval
    cases h1 : u[j]? <;> cases h2 : w[j]? <;> simp_all
    all_goals rename_i b
    all_goals try (cases b <;> simp_all)
    all_goals rename_i b
    all_goals cases b <;> simp_all
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end PEqualNP.Outside.OneHot
