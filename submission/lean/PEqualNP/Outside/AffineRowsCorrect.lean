import PEqualNP.Outside.AffineRowsMachine
import PEqualNP.Outside.UniformWitnessBitEncoding

namespace PEqualNP.Outside.AffineRowsCorrect

open PEqualNP.Library.Universal
open PEqualNP.Outside.AffineHash
open PEqualNP.Outside.AffineRowsMachine (rowBad rowBad_enc check check_enc)
open PEqualNP.Outside.BooleanParityScan (Word parity)
open PEqualNP.Outside.UniformWitnessBitEncoding (code code_bit code_len field)
open PEqualNP.Outside.BoundedWordAffineIsolation (embed)
open PEqualNP.Outside.RecordPairScan (wire)

def bit (a : Coord) : Bool := decide (a = 1)

theorem field_bit (a : Coord) : field (bit a) = a := by
  have h : ∀ a : Coord, field (bit a) = a := by decide
  exact h a

theorem field_xor (a b : Bool) : field (xor a b) = field a + field b := by
  cases a <;> cases b <;> decide

theorem field_and (a b : Bool) : field (a && b) = field a * field b := by
  cases a <;> cases b <;> decide

def products (as bs : Word) : List Coord := List.zipWith (fun a b => field a * field b) as bs

theorem parity_field (as bs : Word) (init : Bool) :
    field (parity as bs init) = field init + (products as bs).sum := by
  induction as generalizing bs init with
  | nil => simp [parity, products]
  | cons a as ih =>
    cases bs with
    | nil => simp [parity, products, ih]
    | cons b bs =>
      simp only [parity, List.tail_cons, List.headD_cons, ih, field_xor, field_and,
        products, List.zipWith_cons_cons, List.sum_cons, add_assoc]

def rowCode {n : ℕ} (r : Row n) : Word := bit r.2 :: List.ofFn (fun i => bit (r.1 i))

def seedCode {n k : ℕ} (h : Seed n k) : Word := wire (List.ofFn (fun i => rowCode (h i)))

theorem products_eq (c w : Word) (hw : w.length ≤ c.length)
    (a : Vec (2 * c.length + 1)) :
    products (List.ofFn (fun i => bit (a i))) (code c w) =
      List.ofFn (fun i => a i * embed c.length w i) := by
  have hlen := code_len c w hw
  apply List.ext_getElem
  · simp [products, hlen]
  · intro i hi₁ hi₂
    have hlt : i < 2 * c.length + 1 := by simpa using hi₂
    have hm : i < (code c w).length := by simpa [hlen] using hlt
    have heb := code_bit c w hw ⟨i, hlt⟩
    rw [List.getElem?_eq_getElem hm] at heb
    change field (code c w)[i] = embed c.length w ⟨i,hlt⟩ at heb
    simp only [products, List.getElem_zipWith, List.getElem_ofFn, field_bit, heb]

theorem row_correct (c w : Word) (hw : w.length ≤ c.length)
    (r : Row (2 * c.length + 1)) :
    rowBad (rowCode r, code c w) = [] ↔ rowEval r (embed c.length w) = 0 := by
  unfold rowCode rowEval dot
  rw [rowBad_enc]
  have he : field (xor (bit r.2) (parity (List.ofFn (fun i => bit (r.1 i))) (code c w) false)) =
      (∑ j, r.1 j * embed c.length w j) + r.2 := by
    rw [field_xor, field_bit, parity_field, products_eq c w hw r.1, List.sum_ofFn]
    simp [field, add_comm]
  rw [← he]
  generalize xor (bit r.2) (parity (List.ofFn (fun i => bit (r.1 i))) (code c w) false) = b
  cases b <;> decide

theorem seed_correct (c w : Word) (hw : w.length ≤ c.length) (k : ℕ)
    (h : Seed (2 * c.length + 1) k) :
    check (seedCode h, code c w) = true ↔ hit h (embed c.length w) := by
  unfold seedCode hit
  rw [check_enc]
  constructor
  · intro hy i
    exact (row_correct c w hw (h i)).mp (hy _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · intro hy r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact (row_correct c w hw (h i)).mpr (hy i)

theorem seed_correct_length (c w : Word) (hw : w.length ≤ c.length) (n k : ℕ)
    (hn : c.length = n) (h : Seed (2 * n + 1) k) :
    check (seedCode h, code c w) = true ↔ hit h (embed n w) := by
  subst n
  exact seed_correct c w hw k h

end PEqualNP.Outside.AffineRowsCorrect
