import PEqualNP.Outside.FirstWideClause

namespace PEqualNP.Outside.WideClauseChoice

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.FirstWideClause (names)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def slot (j : ℕ) (q : Word) : Word := headI (dropI^[j] q)

theorem slot_cpt (j : ℕ) : CPT (slot j) := by
  induction j with
  | zero => exact cpt_headI
  | succ j ih =>
    have h := cpt_comp cpt_dropI ih
    exact cptl h fun q => (congrArg headI (Function.iterate_succ_apply dropI j q)).symm

def choose (q b : Word) : Word :=
  let p₁ := bflag (b.headD false)
  let p₂ := bflag (b.tail.headD false)
  let value := sel p₁ (sel p₂ (slot 0 q) (slot 1 q)) (sel p₂ (slot 2 q) (slot 3 q))
  sel value (slot 0 q) value

theorem choose_cpt {q b : Word → Word} (hq : CPT q) (hb : CPT b) :
    CPT (fun z => choose (q z) (b z)) := by
  have h₁ := cpt_comp hb cpt_firstF
  have h₂ := cpt_comp (cpt_tail1 hb) cpt_firstF
  have hs (i : ℕ) : CPT (fun z => slot i (q z)) := cpt_comp hq (slot_cpt i)
  have value := cpt_sel h₁ (cpt_sel h₂ (hs 0) (hs 1)) (cpt_sel h₂ (hs 2) (hs 3))
  exact cptl (cpt_sel value (hs 0) value) (fun _ => rfl)

def branchIndex (b : Word) : Fin 4 :=
  if b.headD false then
    if b.tail.headD false then 3 else 2
  else
    if b.tail.headD false then 1 else 0

def branchBits (j : Fin 4) (v : Bool) : Word :=
  [decide (2 ≤ j.val), decide (j.val % 2 = 1), v]

theorem branch_index (j : Fin 4) (v : Bool) (b : Word) :
    branchIndex (branchBits j v ++ b) = j := by
  fin_cases j <;> rfl

theorem branch_value (j : Fin 4) (v : Bool) (b : Word) :
    (branchBits j v ++ b).tail.tail.headD false = v := rfl

theorem branch_tail (j : Fin 4) (v : Bool) (b : Word) :
    (branchBits j v ++ b).tail.tail.tail = b := rfl

theorem choose_slot (q b : Word) :
    choose q b = sel (slot (branchIndex b).val q) (slot 0 q) (slot (branchIndex b).val q) := by
  rcases b with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases c <;> rfl

theorem slot_names (c : Clause) (j : ℕ) :
    slot j (names c) = ((c[j]?.map (fun l => vcode l.1))).getD [] := by
  rw [slot, names, dropI_iter_codes]
  by_cases h : j < c.length
  · have h' : j < (c.map Prod.fst).length := by simpa using h
    rw [List.drop_eq_getElem_cons h', List.getElem?_eq_getElem h, List.getElem_map]
    simp [List.flatMap_cons, headI_vcode]
  · have h' : (c.map Prod.fst).length ≤ j := by simpa using Nat.le_of_not_gt h
    rw [List.drop_eq_nil_of_le h', List.getElem?_eq_none (Nat.le_of_not_gt h)]
    rfl

theorem choose_encoded (c : Clause) (b : Word) (j : Fin 4) (v : Literal)
    (hj : branchIndex b = j) (hv : c[j.val]? = some v) :
    choose (names c) b = vcode v.1 := by
  rw [choose_slot, hj, slot_names, hv]
  simp [sel, vcode_ne_nil]

theorem choose_member (c : Clause) (b : Word) (hn : c ≠ []) :
    ∃ l ∈ c, choose (names c) b = vcode l.1 := by
  cases h : c[(branchIndex b).val]? with
  | none =>
    obtain ⟨l, tail, rfl⟩ := List.exists_cons_of_ne_nil hn
    refine ⟨l, by simp, ?_⟩
    rw [choose_slot, slot_names, h]
    simp [sel, slot_names]
  | some l =>
    exact ⟨l, List.mem_of_getElem? h, choose_encoded c b (branchIndex b) l rfl h⟩

end PEqualNP.Outside.WideClauseChoice
