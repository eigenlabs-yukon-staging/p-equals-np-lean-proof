import PEqualNP.Outside.TableauVariableSupport

namespace PEqualNP.Outside.OneHot
open PEqualNP.Library.Universal PEqualNP.Search PEqualNP.Library.SearchHelpers.Tab

def Mentioned (F : CNF) (i : ℕ) : Prop :=
  i ∈ F.flatMap (List.map Prod.fst)

theorem mentioned_of_clause {F : CNF} {cl : Clause} {l : Literal}
    (hc : cl ∈ F) (hl : l ∈ cl) : Mentioned F l.1 :=
  List.mem_flatMap.mpr ⟨cl, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

theorem group_mentioned (c : Code) (zs : List ℕ) (m T : ℕ) {x : ℕ}
    (h : InGroups c.nstk (cellsOf zs.length m T) (bound c) T x) :
    Mentioned (formula c zs m T) x := by
  obtain ⟨⟨n,f⟩, hp, i, hi, rfl⟩ := h
  have hB : 4 ≤ bound c := by unfold bound; omega
  have hn : 2 ≤ n := by
    simp only [groupVars, List.mem_flatMap, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map, List.mem_range, Prod.mk.injEq] at hp
    obtain ⟨t, _, hp⟩ := hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨k, _, j, _, rfl, rfl⟩ <;> omega
  have addClause {cl : Clause} (hcl : cl ∈ pairs n f) : cl ∈ formula c zs m T :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨(n,f), hp, hcl⟩)
  by_cases hz : i = 0
  · subst i
    exact mentioned_of_clause (l := (f 0,false)) (addClause (List.mem_flatMap.mpr
      ⟨1, List.mem_range.mpr (by omega), List.mem_map.mpr
        ⟨0, List.mem_range.mpr (by decide), rfl⟩⟩)) (by simp)
  · exact mentioned_of_clause (l := (f i,false)) (addClause (List.mem_flatMap.mpr
      ⟨i, List.mem_range.mpr hi, List.mem_map.mpr
        ⟨0, List.mem_range.mpr (by omega), rfl⟩⟩)) (by simp)

theorem ghosts_forced (c : Code) (zs : List ℕ) (m T : ℕ) (σ : Assignment)
    (hσ : CNF.eval σ (formula c zs m T) = true) {x : ℕ}
    (hg : Ghost c zs m (cellsOf zs.length m T) x) : σ x = true := by
  obtain ⟨hk,j,hj,rfl⟩ := hg
  apply Snd.imp0
  apply Snd.eval_all hσ
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  unfold initClauses
  apply List.mem_append_right
  rw [if_pos hk]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem on_used (c : Code) (zs : List ℕ) (m T : ℕ) (hz : ∀ z ∈ zs, z < 4)
    (σ : Assignment) (hσ : CNF.eval σ (formula c zs m T) = true) (w : List Bool)
    (hw : w.length ≤ m) (h : c.outputsWithin (inputOf zs w) T [1])
    (ha : Agrees c zs m T w σ) :
    ∀ x, Mentioned (formula c zs m T) x → σ x = Cpl.asg c (inputOf zs w) x := by
  intro x hx
  unfold Mentioned at hx
  obtain ⟨cl,hcl,hmap⟩ := List.mem_flatMap.mp hx
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hmap
  rcases formula_support c zs m T hz cl hcl l hl with ⟨p,hp,i,hi,he⟩ | hg
  · rw [← he]
    exact ha p hp i hi
  · rw [ghosts_forced c zs m T σ hσ hg,
      ghosts_forced c zs m T _ (canonical_model c zs m T w hw h) hg]


def extend (F : CNF) (a : {i : ℕ // Mentioned F i} → Bool) : Assignment :=
  fun i => if h : i ∈ F.flatMap (List.map Prod.fst) then a ⟨i,h⟩ else false

theorem eval_ext {F : CNF} {σ τ : Assignment}
    (h : ∀ i, Mentioned F i → σ i = τ i) : CNF.eval σ F = CNF.eval τ F := by
  have clause (cl : Clause) (hc : cl ∈ F) :
      Clause.eval σ cl = true ↔ Clause.eval τ cl = true := by
    simp only [Clause.eval, List.any_eq_true]
    exact exists_congr (fun l => and_congr_right (fun hl => by
      simp only [Literal.eval, h l.1 (mentioned_of_clause hc hl)]))
  have equiv : CNF.eval σ F = true ↔ CNF.eval τ F = true := by
    simp only [CNF.eval, List.all_eq_true]
    exact forall_congr' (fun cl => imp_congr_right (clause cl))
  cases hσ : CNF.eval σ F <;> cases hτ : CNF.eval τ F <;> simp_all

theorem eval_restrict (F : CNF) (σ : Assignment) :
    CNF.eval (extend F (fun i => σ i.1)) F = CNF.eval σ F := by
  apply eval_ext
  intro i hi
  exact dite_eq_left hi

def Witnesses (c : Code) (zs : List ℕ) (m T : ℕ) :=
  {w : List Bool // w.length ≤ m ∧ c.outputsWithin (inputOf zs w) T [1]}

def Models (F : CNF) :=
  {a : {i : ℕ // Mentioned F i} → Bool // CNF.eval (extend F a) F = true}

noncomputable def restrict_model (c : Code) (zs : List ℕ) (m T : ℕ) (w : Witnesses c zs m T) :
    Models (formula c zs m T) :=
  ⟨fun i => Cpl.asg c (inputOf zs w.1) i.1,
    (eval_restrict ..).trans (canonical_model c zs m T w.1 w.2.1 w.2.2)⟩

noncomputable def models_equiv (c : Code) (zs : List ℕ) (m T : ℕ)
    (hz : ∀ z ∈ zs, z < 4) (hk : c.kin < c.nstk) :
    Witnesses c zs m T ≃ Models (formula c zs m T) := by
  apply Equiv.ofBijective (restrict_model c zs m T)
  constructor
  · intro u w he
    apply Subtype.ext
    have hw : Agrees c zs m T w.1 (Cpl.asg c (inputOf zs u.1)) := by
      intro p hp i hi
      let k : {x : ℕ // Mentioned (formula c zs m T) x} :=
        ⟨p.2 i, group_mentioned c zs m T ⟨p, hp, i, hi, rfl⟩⟩
      exact congrFun (congrArg Subtype.val he) k
    exact unique_witness hk u.2.1 w.2.1 (fun _ _ _ _ => rfl) hw
  · intro a
    obtain ⟨w,hw,ha,hagree⟩ := decode c zs m T hz (extend _ a.1) a.2
    refine ⟨⟨w,hw,ha⟩, Subtype.ext (funext fun i => ?_)⟩
    have h := on_used c zs m T hz (extend _ a.1) a.2 w hw ha hagree i.1 i.2
    exact h.symm.trans (dite_eq_left i.2)

end PEqualNP.Outside.OneHot

open PEqualNP.Library.Universal PEqualNP.Search PEqualNP.Library.SearchHelpers.Tab

theorem PEqualNP.Outside.ParsimoniousTableau :
    ∀ (c : Code) (zs : List ℕ) (m T : ℕ), (∀ z ∈ zs, z < 4) → c.kin < c.nstk →
      ∃ add : CNF, IsKCNF 2 add ∧
        let φ := tableau c zs m T ++ add
        Nonempty ({w : List Bool // w.length ≤ m ∧
                    c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1]} ≃
                  {a : {i : ℕ // i ∈ φ.flatMap (List.map Prod.fst)} → Bool //
                    CNF.eval (fun i => if h : i ∈ φ.flatMap (List.map Prod.fst)
                      then a ⟨i,h⟩ else false) φ = true}) := by
  intro c zs m T hz hk
  refine ⟨PEqualNP.Outside.OneHot.strengthening c.nstk (cellsOf zs.length m T) (bound c) T,
    ?_, ⟨PEqualNP.Outside.OneHot.models_equiv c zs m T hz hk⟩⟩
  unfold IsKCNF PEqualNP.Outside.OneHot.strengthening PEqualNP.Outside.OneHot.pairs
  intro cl hc
  obtain ⟨⟨n,f⟩, _, h⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, _, h⟩ := List.mem_flatMap.mp h
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
  simp
