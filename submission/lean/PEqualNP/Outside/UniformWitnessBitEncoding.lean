import PEqualNP.Outside.BoundedWordAffineIsolation
import PEqualNP.Outside.SatCodePrimitives

namespace PEqualNP.Outside.UniformWitnessBitEncoding

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BoundedWordAffineIsolation (embed)

abbrev Word := List Bool
local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def fill (b : Bool) (s : Word) : Word := s.map (fun _ => b)

theorem fill_cpt (b : Bool) : CPT (fill b) :=
  filterMap_polyTime _ _ _ (fun _ => some b) (fun s => by simp [fill])

theorem fill_eq (b : Bool) (s : Word) : fill b s = List.replicate s.length b := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [fill, List.replicate_succ] at ih ⊢

private theorem iterate_tail (k : ℕ) (s : Word) : List.tail^[k] s = s.drop k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases s <;> simp

def pad (c w : Word) : Word := List.tail^[w.length] (fill false c)

def code (c w : Word) : Word := (fill true w ++ false :: pad c w) ++ (w ++ pad c w)

theorem code_cpt : ComputableInPolyTime encodePair (fun x : Word => x) (fun q : Word × Word => code q.1 q.2) := by
  have hfill := cpt_comp cpt_unpairB1 (fill_cpt false)
  have hpad := cpt_iterLen cpt_tail (fun s => by simp [List.length_tail]) cpt_unpairB2 hfill
  have hone := cpt_comp cpt_unpairB2 (fill_cpt true)
  have h := cpt_app2 (cpt_app2 hone (cpt_cons1 false hpad)) (cpt_app2 cpt_unpairB2 hpad)
  exact cptl (cpt_comp cpt_pairB h) (fun _ => by simp [code, pad, unpairB_pairB])

theorem pad_eq (c w : Word) : pad c w = List.replicate (c.length - w.length) false := by
  rw [pad, iterate_tail, fill_eq, List.drop_replicate]

def head (n : ℕ) (w : Word) : Word :=
  List.replicate w.length true ++ List.replicate (n + 1 - w.length) false

def payload (n : ℕ) (w : Word) : Word := w ++ List.replicate (n - w.length) false

theorem code_eq (c w : Word) (h : w.length ≤ c.length) :
    code c w = head c.length w ++ payload c.length w := by
  simp only [code, head, payload, fill_eq, pad_eq]
  rw [show c.length + 1 - w.length = c.length - w.length + 1 by omega, List.replicate_succ]

theorem head_len (n : ℕ) (w : Word) (h : w.length ≤ n) : (head n w).length = n + 1 := by
  simp only [head, List.length_append, List.length_replicate]
  omega

theorem payload_len (n : ℕ) (w : Word) (h : w.length ≤ n) : (payload n w).length = n := by
  simp only [payload, List.length_append, List.length_replicate]
  omega

theorem code_len (c w : Word) (hw : w.length ≤ c.length) :
    (code c w).length = 2 * c.length + 1 := by
  rw [code_eq c w hw, List.length_append, head_len _ _ hw, payload_len _ _ hw]
  omega

def field (b : Bool) : ZMod 2 := if b then 1 else 0

theorem code_bit (c w : Word) (hw : w.length ≤ c.length) (j : Fin (2 * c.length + 1)) :
    field ((code c w)[j.val]?.getD false) = embed c.length w j := by
  rw [code_eq c w hw]
  have hh := head_len c.length w hw
  by_cases h : j.val ≤ c.length
  · have hl : j.val < (head c.length w).length := by omega
    rw [List.getElem?_append_left hl]
    unfold head embed
    rw [if_pos h]
    by_cases ht : j.val < w.length
    · have hr : j.val < (List.replicate w.length true).length := by simpa using ht
      rw [List.getElem?_append_left hr]
      simp [List.getElem?_replicate, ht, field]
    · have hr : (List.replicate w.length true).length ≤ j.val := by simpa using Nat.le_of_not_gt ht
      rw [List.getElem?_append_right hr]
      simp [List.getElem?_replicate, ht, field]
      split <;> rfl
  · have hl : (head c.length w).length ≤ j.val := by omega
    rw [List.getElem?_append_right hl, hh]
    unfold payload embed
    rw [if_neg h]
    by_cases ht : j.val - (c.length + 1) < w.length
    · rw [List.getElem?_append_left ht]
      rfl
    · rw [List.getElem?_append_right (Nat.le_of_not_gt ht)]
      simp [List.getElem?_eq_none (Nat.le_of_not_gt ht), List.getElem?_replicate, field]
      split <;> rfl

end PEqualNP.Outside.UniformWitnessBitEncoding
