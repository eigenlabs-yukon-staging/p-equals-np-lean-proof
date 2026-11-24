import PEqualNP.Outside.BoundedWordAffineIsolation
import PEqualNP.Defs

namespace PEqualNP.Outside.NPWitnessIsolation

abbrev Word := List Bool

def words : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 => insert [] (((words n).image (false :: ·)) ∪ ((words n).image (true :: ·)))

theorem mem_words (n : ℕ) (w : Word) : w ∈ words n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons b w => cases b <;> simp [words, ih]

noncomputable def goodWords (R : Set (Word × Word)) (p : Polynomial ℕ) (x : Word) : Finset Word :=
  open Classical in
  (words (p.eval x.length)).filter (fun w => (x,w) ∈ R)

theorem mem_goodWords (R : Set (Word × Word)) (p : Polynomial ℕ) (x w : Word) :
    w ∈ goodWords R p x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R := by
  simp [goodWords, mem_words]

end PEqualNP.Outside.NPWitnessIsolation

open PEqualNP.Library
open PEqualNP.Outside.BoundedWordAffineIsolation (embed)
open PEqualNP.Outside.NPWitnessIsolation

theorem PEqualNP.Outside.BoundedNPWitnessIsolation :
    ∀ L : Language Bool, L ∈ NP →
      ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ)
        (E : (b : ℕ) → List Bool → (Fin (2 * b + 1) → ZMod 2))
        (W : List Bool → Finset (List Bool)),
        DecidableInPolyTime encodePair R ∧
        (∀ x w, w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R) ∧
        (∀ x, x ∈ L ↔ (W x).Nonempty) ∧
        (∀ b, Set.InjOn (E b) ({w : List Bool | w.length ≤ b} : Set (List Bool))) ∧
        ∀ x ∈ L,
          let b := p.eval x.length
          let n := 2 * b + 1
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ n + 2 ∧
            Fintype.card (Fin k → ((Fin n → ZMod 2) × ZMod 2)) ≤ 8 *
              ((Finset.univ : Finset (Fin k → ((Fin n → ZMod 2) × ZMod 2))).filter (fun f =>
                ∃ w ∈ W x, (∀ i, (∑ j : Fin n, (f i).1 j * E b w j) + (f i).2 = 0) ∧
                  ∀ v ∈ W x, v ≠ w → ¬ (∀ i, (∑ j : Fin n, (f i).1 j * E b v j) + (f i).2 = 0))).card := by
  intro L hL
  obtain ⟨R, p, hR, hspec⟩ := hL
  let W := goodWords R p
  have hW (x w : List Bool) : w ∈ W x ↔ w.length ≤ p.eval x.length ∧ (x,w) ∈ R :=
    mem_goodWords R p x w
  have hx (x : List Bool) : x ∈ L ↔ (W x).Nonempty := by
    refine (hspec x).trans ?_
    exact exists_congr (fun w => (hW x w).symm)
  choose E hE using PEqualNP.Outside.BoundedWordAffineIsolation
  refine ⟨R, p, E, W, hR, hW, hx, (fun b => (hE b).1), ?_⟩
  intro x h
  have hw := (hE (p.eval x.length)).2 (W x) ((hx x).mp h) (fun w hw => ((hW x w).mp hw).1)
  exact hw
