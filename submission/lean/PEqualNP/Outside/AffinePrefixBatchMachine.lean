import PEqualNP.Outside.RecordBlockSplit
import PEqualNP.Outside.AffineWitnessVerifier
import PEqualNP.Outside.FiniteSeedPrefix

namespace PEqualNP.Outside.AffinePrefixBatchMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word)
open PEqualNP.Outside.AffineHash (Seed)
open PEqualNP.Outside.AffineRowsCorrect (rowCode seedCode)
open PEqualNP.Outside.AffineWitnessVerifier (encodedSeed)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.FiniteSeedPrefix (takeRows)
open PEqualNP.Outside.RecordPrefixQueries (batch batch_cpt batch_enc listFrom)
open PEqualNP.Outside.RecordBlockSplit (split split_cpt split_enc)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)

def width (p : Polynomial ℕ) (x : Word) : Word :=
  true :: true :: (un (p.eval x.length) ++ un (p.eval x.length))

theorem width_cpt (p : Polynomial ℕ) : CPT (width p) :=
  cpt_cons1 true (cpt_cons1 true (cpt_app2 (L055 p) (L055 p)))

theorem width_length (p : Polynomial ℕ) (x : Word) :
    (width p x).length = 2 * p.eval x.length + 2 := by
  simp only [width, List.length_cons, List.length_append, un_length]
  omega

def rows (p : Polynomial ℕ) (q : Word × Word) : Word := split (width p q.1, q.2)

theorem rows_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun w : Word => w) (rows p) := by
  have hw := cpt_comp (f := Prod.fst) (g := width p) cpt_fst (width_cpt p)
  have hp := cpt_pairG (f := fun q : Word × Word => width p q.1) (g := Prod.snd) hw cpt_snd
  unfold rows
  exact cpt_comp (f := fun q : Word × Word => (width p q.1, q.2)) (g := split) hp split_cpt

def produce (p : Polynomial ℕ) (q : Word × Word) : Word := batch (q.1, rows p q)

theorem produce_cpt (p : Polynomial ℕ) :
    ComputableInPolyTime encodePair (fun w : Word => w) (produce p) := by
  have hp := cpt_pairG (f := Prod.fst) (g := rows p) cpt_fst (rows_cpt p)
  unfold produce
  exact cpt_comp (f := fun q : Word × Word => (q.1, rows p q)) (g := batch) hp batch_cpt

def matrixRows (b k : ℕ) (f : Seed (2 * b + 1) k) : List Word := List.ofFn (fun i => rowCode (f i))

def matrixWord (b k : ℕ) (f : Seed (2 * b + 1) k) : Word := (matrixRows b k f).flatten

theorem row_length {b k : ℕ} (f : Seed (2 * b + 1) k) (r : Word) (hr : r ∈ matrixRows b k f) :
    r.length = 2 * b + 2 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  simp [rowCode, Nat.add_assoc]

theorem matrix_length (b k : ℕ) (f : Seed (2 * b + 1) k) :
    (matrixWord b k f).length = k * (2 * b + 2) := by
  rw [matrixWord, List.length_flatten]
  have he : (matrixRows b k f).map List.length =
      List.replicate (matrixRows b k f).length (2 * b + 2) :=
    List.map_eq_replicate_iff.mpr (fun r hr => row_length f r hr)
  rw [he, List.sum_replicate]
  simp [matrixRows]

theorem produce_enc (p : Polynomial ℕ) (x : Word) (m : ℕ)
    (f : Seed (2 * p.eval x.length + 1) m) :
    produce p (x, matrixWord (p.eval x.length) m f) =
      wire (listFrom x [] (matrixRows (p.eval x.length) m f)) := by
  unfold produce rows matrixWord
  rw [split_enc (width p x) (matrixRows (p.eval x.length) m f) (by simp [width])
    (fun r hr => (row_length f r hr).trans (width_length p x).symm), batch_enc]

theorem mem_listFrom (x : Word) (pref rs : List Word) (z : Word) :
    z ∈ listFrom x pref rs ↔
      ∃ k : ℕ, 0 < k ∧ k ≤ rs.length ∧ z = pairB x (wire (pref ++ rs.take k)) := by
  induction rs generalizing pref with
  | nil => simp [listFrom]
  | cons r rs ih =>
    simp only [listFrom, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨k,hk,hl,rfl⟩)
      · exact ⟨1, by omega, by simp, by simp⟩
      · exact ⟨k+1, by omega, by simpa using hl, by simp [List.append_assoc]⟩
    · rintro ⟨k, hk, hl, rfl⟩
      cases k with
      | zero => omega
      | succ k =>
        by_cases h : k = 0
        · subst k
          simp
        · exact Or.inr ⟨k, Nat.pos_of_ne_zero h, by simpa using hl, by simp [List.append_assoc]⟩

theorem take_matrix (b m k : ℕ) (hk : k ≤ m) (f : Seed (2 * b + 1) m) :
    (matrixRows b m f).take k = matrixRows b k (takeRows hk f) := by
  apply List.ext_getElem
  · simp [matrixRows, Nat.min_eq_left hk]
  · intro j hj₁ hj₂
    simp only [matrixRows, List.getElem_take, List.getElem_ofFn, takeRows]

theorem mem_queries (b m : ℕ) (x z : Word) (f : Seed (2 * b + 1) m) :
    z ∈ listFrom x [] (matrixRows b m f) ↔
      ∃ k : Fin (m + 1), 0 < k.val ∧ z = pairB x (encodedSeed b k.val (takeRows
        (Nat.le_of_lt_succ k.isLt) f)) := by
  rw [mem_listFrom]
  simp only [matrixRows, List.length_ofFn, List.nil_append]
  constructor
  · rintro ⟨k, hk, hm, he⟩
    refine ⟨⟨k, Nat.lt_succ_of_le hm⟩, hk, ?_⟩
    rw [he]
    congr 2
    exact take_matrix b m k hm f
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.val, hk, Nat.le_of_lt_succ k.isLt, ?_⟩
    change pairB x (wire (matrixRows b k.val (takeRows (Nat.le_of_lt_succ k.isLt) f))) =
      pairB x (wire ((matrixRows b m f).take k.val))
    rw [take_matrix b m k.val (Nat.le_of_lt_succ k.isLt) f]

end PEqualNP.Outside.AffinePrefixBatchMachine
