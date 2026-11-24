import PEqualNP.Outside.FiniteFixedBooleanAssignments
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PEqualNP.Outside.UniqueTernaryCount
open PEqualNP.Search
open PEqualNP.Outside.FixedBooleanAssignments (agrees count)

def assign {n : ℕ} (a : Fin n → Bool) : Assignment :=
  fun i => if h : i < n then a ⟨i,h⟩ else false

def bad (n : ℕ) (c : Clause) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun a => Clause.eval (assign a) c = false)

private theorem bool_ne (x y : Bool) : x ≠ y ↔ x = !y := by
  cases x <;> cases y <;> decide

theorem bad_card (n : ℕ) (c : Clause)
    (h : c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) :
    (bad n c).card * 8 = 2^n := by
  rcases h with ⟨hL,hN,hB⟩
  rcases c with _ | ⟨a,_ | ⟨b,_ | ⟨d,cs⟩⟩⟩
  · cases hL
  · cases hL
  · cases hL
  have hs : cs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hL; omega)
  subst cs
  let i : Fin n := ⟨a.1,hB a (by simp)⟩
  let j : Fin n := ⟨b.1,hB b (by simp)⟩
  let k : Fin n := ⟨d.1,hB d (by simp)⟩
  have hd : a.1 ≠ b.1 ∧ a.1 ≠ d.1 ∧ b.1 ≠ d.1 := by
    simpa [List.nodup_cons,and_assoc] using hN
  have hij : i ≠ j := fun e => hd.1 (congrArg Fin.val e)
  have hik : i ≠ k := fun e => hd.2.1 (congrArg Fin.val e)
  have hjk : j ≠ k := fun e => hd.2.2 (congrArg Fin.val e)
  let S : Finset (Fin n) := {i,j,k}
  let fixed : Fin n → Bool := fun q => if q = i then !a.2 else if q = j then !b.2 else !d.2
  have hCard : S.card = 3 := by simp [S,hij,hik,hjk]
  have hEq : bad n [a,b,d] = @Finset.filter (Fin n → Bool)
      (fun f => agrees S fixed f) (fun _ => Classical.propDecidable _) Finset.univ := by
    ext f
    simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and]
    have hi : assign f a.1 = f i := dif_pos (hB a (by simp))
    have hj : assign f b.1 = f j := dif_pos (hB b (by simp))
    have hk : assign f d.1 = f k := dif_pos (hB d (by simp))
    have h' : Clause.eval (assign f) [a,b,d] = false ↔
        f i = !a.2 ∧ f j = !b.2 ∧ f k = !d.2 := by
      simp [Clause.eval,Literal.eval,hi,hj,hk,Bool.or_eq_false_iff,bool_ne]
    rw [h']
    constructor
    · rintro ⟨ha,hb,hd'⟩ q hq
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · simpa [fixed] using ha
      · simpa [fixed,Ne.symm hij] using hb
      · simpa [fixed,Ne.symm hik,Ne.symm hjk] using hd'
    · intro ha
      exact ⟨by simpa [fixed] using ha i (by simp [S]),
        by simpa [fixed,Ne.symm hij] using ha j (by simp [S]),
        by simpa [fixed,Ne.symm hik,Ne.symm hjk] using ha k (by simp [S])⟩
  rw [hEq]
  simpa only [hCard,show (2:ℕ)^3 = 8 by decide] using count n S fixed

theorem cover_eq (n : ℕ) (F : CNF) :
    (Finset.univ : Finset (Fin F.length)).biUnion (fun i => bad n (F.get i)) =
      (Finset.univ : Finset (Fin n → Bool)).filter (fun a => CNF.eval (assign a) F = false) := by
  ext a
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,bad,Finset.mem_filter]
  have he : (∃ i : Fin F.length, Clause.eval (assign a) (F.get i) = false) ↔
      ∃ c ∈ F, Clause.eval (assign a) c = false := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨F.get i,List.get_mem ..,hi⟩
    · rintro ⟨c,hc,hB⟩
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
      exact ⟨⟨i,hi⟩,hB⟩
  rw [he]
  cases he' : CNF.eval (assign a) F
  · have hn : ¬ ∀ c ∈ F, Clause.eval (assign a) c = true := by
      simpa [CNF.eval,List.all_eq_true] using (show ¬ CNF.eval (assign a) F = true by simp [he'])
    push Not at hn
    simp only [Bool.not_eq_true] at hn
    exact ⟨fun _ => rfl,fun _ => hn⟩
  · have hn : ∀ c ∈ F, Clause.eval (assign a) c = true := List.all_eq_true.mp he'
    exact ⟨fun ⟨c,hc,hF⟩ => (Bool.noConfusion (hF.symm.trans (hn c hc))),fun hF => Bool.noConfusion hF⟩

theorem bad_fac (n : ℕ) (F : CNF)
    (h : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun a => CNF.eval (assign a) F = false)).card * 8 ≤
      F.length * 2^n := by
  let U := (Finset.univ : Finset (Fin F.length)).biUnion (fun i => bad n (F.get i))
  have hU := cover_eq n F
  rw [← hU]
  calc
    U.card * 8 ≤ (∑ i : Fin F.length, (bad n (F.get i)).card) * 8 :=
      Nat.mul_le_mul_right 8 Finset.card_biUnion_le
    _ = F.length * 2^n := by
      rw [Finset.sum_mul]
      simp only [bad_card n _ (h _ (List.get_mem ..)),Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem unique_bad_count (n : ℕ) (F : CNF)
    (hu : ∃! a : Fin n → Bool, CNF.eval (assign a) F = true) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun b => CNF.eval (assign b) F = false)).card +
      1 = 2^n := by
  classical
  obtain ⟨a,ha,hu⟩ := hu
  have hSet : ((Finset.univ : Finset (Fin n → Bool)).filter (fun b => CNF.eval (assign b) F = true)) = {a} := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨hu _,fun e => e.symm ▸ ha⟩
  have hUnion : ((Finset.univ : Finset (Fin n → Bool)).filter (fun b => CNF.eval (assign b) F = false)).card +
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun b => CNF.eval (assign b) F = true)).card = 2^n := by
    have he := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n → Bool))) (fun b => CNF.eval (assign b) F = false)
    simpa [Fintype.card_fun,Bool.not_eq_false] using he
  rw [hSet,Finset.card_singleton] at hUnion
  exact hUnion

theorem lower (n : ℕ) (F : CNF) (hn : 4 ≤ n)
    (h : ∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n)
    (hu : ∃! a : Fin n → Bool, CNF.eval (assign a) F = true) : 8 ≤ F.length := by
  have hUnion := unique_bad_count n F hu
  have hCount := bad_fac n F h
  by_contra hl
  have hlen : F.length ≤ 7 := by omega
  have hC := hCount.trans (Nat.mul_le_mul_right (2^n) hlen)
  have hn' : 16 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  omega

end PEqualNP.Outside.UniqueTernaryCount

open PEqualNP.Search

theorem PEqualNP.Outside.UniqueTernaryClauseLowerBound :
    ∀ (n : ℕ) (F : CNF), 4 ≤ n →
      (∀ c ∈ F, c.length = 3 ∧ (c.map Prod.fst).Nodup ∧ ∀ l ∈ c, l.1 < n) →
      (∃! a : Fin n → Bool,
        CNF.eval (fun i => if h : i < n then a ⟨i,h⟩ else false) F = true) →
      8 ≤ F.length := by
  exact PEqualNP.Outside.UniqueTernaryCount.lower
