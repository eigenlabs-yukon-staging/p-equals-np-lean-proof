import PEqualNP.Outside.WideClauseChoice

namespace PEqualNP.Outside.BoundedWidthChoice

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.FirstWideClause (names)
open PEqualNP.Outside.WideClauseChoice (Word slot slot_cpt slot_names)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def index : ℕ → Word → ℕ
  | 0, _ => 0
  | m + 1, b =>
    (if b.headD false then 2 ^ m else 0) + index m b.tail

def indexBits : ℕ → ℕ → Word
  | 0, _ => []
  | m + 1, j =>
    if j < 2 ^ m then false :: indexBits m j
    else true :: indexBits m (j - 2 ^ m)

theorem prefix_length (m j : ℕ) : (indexBits m j).length = m := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    simp only [indexBits]
    split <;> simp [ih]

theorem index_prefix (m j : ℕ) (b : Word) (h : j < 2 ^ m) :
    index m (indexBits m j ++ b) = j := by
  induction m generalizing j with
  | zero => simp at h; subst j; rfl
  | succ m ih =>
    by_cases hlt : j < 2 ^ m
    · simp [indexBits, index, hlt, ih j hlt]
    · have ht : j - 2 ^ m < 2 ^ m := by
        rw [pow_succ] at h
        omega
      simp [indexBits, index, hlt, ih _ ht]
      omega

def branchBits (m j : ℕ) (v : Bool) : Word := indexBits m j ++ [v]

theorem code_length (m j : ℕ) (v : Bool) : (branchBits m j v).length = m + 1 := by
  simp [branchBits, prefix_length]

theorem branch_index (m j : ℕ) (v : Bool) (b : Word) (h : j < 2 ^ m) :
    index m (branchBits m j v ++ b) = j := by
  simpa [branchBits, List.append_assoc] using index_prefix m j (v :: b) h

theorem branch_value (m j : ℕ) (v : Bool) (b : Word) :
    ((branchBits m j v ++ b).drop m).headD false = v := by
  simp only [branchBits, List.append_assoc, List.singleton_append,
    List.drop_left' (prefix_length m j), List.headD_cons]

theorem branch_tail (m j : ℕ) (v : Bool) (b : Word) :
    (branchBits m j v ++ b).drop (m + 1) = b := by
  rw [← code_length m j v]
  simp

def walk : ℕ → ℕ → Word → Word → Word
  | 0, lo, q, _ => slot lo q
  | m + 1, lo, q, b => sel (bflag (b.headD false)) (walk m lo q b.tail)
      (walk m (lo + 2 ^ m) q b.tail)

theorem walk_cpt (m lo : ℕ) {q b : Word → Word} (hq : CPT q) (hb : CPT b) :
    CPT (fun z => walk m lo (q z) (b z)) := by
  induction m generalizing lo b with
  | zero => exact cpt_comp hq (slot_cpt lo)
  | succ m ih =>
    have h := cpt_sel (cpt_comp hb cpt_firstF)
      (ih lo (cpt_tail1 hb)) (ih (lo + 2 ^ m) (cpt_tail1 hb))
    exact h

theorem walk_index (m lo : ℕ) (q b : Word) :
    walk m lo q b = slot (lo + index m b) q := by
  induction m generalizing lo b with
  | zero => simp [walk, index]
  | succ m ih =>
    cases h : b.head?.getD false <;>
      simp [walk, index, sel, bflag, h, ih, Nat.add_assoc]

def choose (m : ℕ) (q b : Word) : Word :=
  let w := walk m 0 q b
  sel w (slot 0 q) w

theorem choose_cpt (m : ℕ) {q b : Word → Word} (hq : CPT q) (hb : CPT b) :
    CPT (fun z => choose m (q z) (b z)) := by
  have h := walk_cpt m 0 hq hb
  have hm := cpt_comp hq (slot_cpt 0)
  exact cptl (cpt_sel h hm h) (fun _ => rfl)

theorem choose_slot (m : ℕ) (q b : Word) :
    choose m q b = sel (slot (index m b) q) (slot 0 q) (slot (index m b) q) := by
  simp [choose, walk_index]

theorem choose_encoded (m : ℕ) (c : Clause) (b : Word) (j : ℕ) (v : Literal)
    (hj : index m b = j) (hv : c[j]? = some v) :
    choose m (names c) b = vcode v.1 := by
  rw [choose_slot, hj, slot_names, hv]
  simp [sel, vcode_ne_nil]

theorem choose_member (m : ℕ) (c : Clause) (b : Word) (hn : c ≠ []) :
    ∃ l ∈ c, choose m (names c) b = vcode l.1 := by
  cases h : c[index m b]? with
  | none =>
    obtain ⟨l, tail, rfl⟩ := List.exists_cons_of_ne_nil hn
    refine ⟨l, by simp, ?_⟩
    rw [choose_slot, slot_names, h]
    simp [sel, slot_names]
  | some l =>
    exact ⟨l, List.mem_of_getElem? h, choose_encoded m c b (index m b) l rfl h⟩

end PEqualNP.Outside.BoundedWidthChoice
