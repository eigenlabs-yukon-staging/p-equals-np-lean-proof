import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace PEqualNP.Outside.PolynomialEvaluationSeparation

open Polynomial

variable {F : Type} [Field F]

noncomputable def bitPolynomial (n : ℕ) (u : Fin n → Bool) : F[X] :=
  ∑ i : Fin n, monomial i.val (if u i then 1 else 0)

theorem coeff_bit (n : ℕ) (u : Fin n → Bool) (i : Fin n) :
    (bitPolynomial (F := F) n u).coeff i.val = if u i then 1 else 0 := by
  classical
  simp only [bitPolynomial, finsetSum_coeff, coeff_monomial, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have h : j.val ≠ i.val := fun he => hj (Fin.ext he)
    simp [h, Ne.symm h]
  · simp

theorem bit_inj (n : ℕ) : Function.Injective (bitPolynomial (F := F) n) := by
  intro u v h
  funext i
  have hc := congrArg (fun p : F[X] => p.coeff i.val) h
  rw [coeff_bit, coeff_bit] at hc
  cases hu : u i <;> cases hv : v i <;> simp [hu,hv] at hc ⊢

theorem bit_degree (n : ℕ) (u : Fin n → Bool) :
    (bitPolynomial (F := F) n u).natDegree ≤ n := by
  unfold bitPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans i.isLt.le

theorem eval_bit (n : ℕ) (u : Fin n → Bool) (a : F) :
    (bitPolynomial n u).eval a = ∑ i : Fin n, (if u i then 1 else 0) * a ^ i.val := by
  simp [bitPolynomial, eval_finsetSum, eval_monomial]

noncomputable def collisions (n : ℕ) (q : (Fin n → Bool) × (Fin n → Bool)) : Finset F := by
  classical
  exact if q.1 = q.2 then ∅ else ((bitPolynomial n q.1) - (bitPolynomial n q.2)).roots.toFinset

theorem collision_bound (n : ℕ) (q : (Fin n → Bool) × (Fin n → Bool)) :
    (collisions (F := F) n q).card ≤ n := by
  classical
  by_cases he : q.1 = q.2
  · simp [collisions, he]
  · simp only [collisions, if_neg he]
    apply (Multiset.toFinset_card_le _).trans
    apply (card_roots' _).trans
    simpa only [max_self] using natDegree_sub_le_of_le (bit_degree (F := F) n q.1) (bit_degree (F := F) n q.2)

theorem separation [Fintype F] (n : ℕ) (S : Finset (Fin n → Bool))
    (hF : Fintype.card F > S.card * S.card * n) :
    ∃ a : F, Set.InjOn (fun u => (bitPolynomial n u).eval a) (S : Set (Fin n → Bool)) := by
  classical
  let bad := (S.product S).biUnion (collisions (F := F) n)
  have hb : bad.card ≤ S.card * S.card * n := by
    unfold bad
    rw [← Finset.card_product]
    exact Finset.card_biUnion_le_card_mul _ _ _ (fun q _ => collision_bound n q)
  have hg : ∃ a : F, a ∉ bad := by
    by_contra h
    have hle : (Finset.univ : Finset F).card ≤ bad.card :=
      Finset.card_le_card (fun a _ => Classical.byContradiction (fun hn => h ⟨a,hn⟩))
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨a, ha⟩ := hg
  refine ⟨a,?_⟩
  intro u hu v hv he
  by_contra hd
  apply ha
  apply Finset.mem_biUnion.mpr
  refine ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, ?_⟩
  simp only [collisions, if_neg hd, Multiset.mem_toFinset]
  have hn : bitPolynomial (F := F) n u - bitPolynomial n v ≠ 0 :=
    sub_ne_zero.mpr (fun hh => hd (bit_inj n hh))
  apply (mem_roots hn).mpr
  change (bitPolynomial (F := F) n u - bitPolynomial n v).eval a = 0
  rw [eval_sub]
  exact sub_eq_zero.mpr he

end PEqualNP.Outside.PolynomialEvaluationSeparation

open PEqualNP.Outside.PolynomialEvaluationSeparation

theorem PEqualNP.Outside.PolynomialEvaluationSeparation :
    ∀ (n : ℕ) (S : Finset (Fin n → Bool)),
      ∃ q : ℕ, Nat.Prime q ∧ S.card * S.card * n < q ∧ q ≤ 2 * (S.card * S.card * n + 1) ∧
        ∃ a : ZMod q, Set.InjOn (fun u =>
          ∑ i : Fin n, (if u i then (1 : ZMod q) else 0) * a ^ i.val) (S : Set (Fin n → Bool)) := by
  intro n S
  obtain ⟨q, hq, hl, hh⟩ := Nat.exists_prime_lt_and_le_two_mul (S.card*S.card*n+1) (by omega)
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hlarge : S.card * S.card * n < Fintype.card (ZMod q) := by rw [ZMod.card]; omega
  obtain ⟨a, ha⟩ := separation (F := ZMod q) n S hlarge
  exact ⟨q,hq,by omega,hh,a,by simpa only [eval_bit] using ha⟩
