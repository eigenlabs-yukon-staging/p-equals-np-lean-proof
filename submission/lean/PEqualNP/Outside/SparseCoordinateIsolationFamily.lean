import PEqualNP.Outside.SparseCoordinateSeparation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

namespace PEqualNP.Outside.SparseCoordinateIsolation

open PEqualNP.Outside.SparseCoordinateSeparation (separate)

abbrev Pattern (n c : ℕ) := Fin c → Option (Fin n × Bool)

def permits {n c : ℕ} (p : Pattern n c) (u : Fin n → Bool) : Prop :=
  ∀ i : Fin c, (p i).elim True (fun q => u q.1 = q.2)

theorem per_pattern {n c : ℕ} (S : Finset (Fin n → Bool)) (hc : S.card ≤ c + 1) (u : Fin n → Bool)
    (hu : u ∈ S) :
    ∃ p : Pattern n c, ∀ v ∈ S, permits p v ↔ v = u := by
  classical
  obtain ⟨C,hC,hsep⟩ := separate S
  let p (j : Fin c) : Option (Fin n × Bool) :=
    (C.toList[j.val]?).map (fun i => (i,u i))
  refine ⟨p, ?_⟩
  intro v hv
  constructor
  · intro hp
    apply hsep v hv u hu
    intro i hi
    have hm : i ∈ C.toList := Finset.mem_toList.mpr hi
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hm
    have hlen : C.toList.length ≤ c := by
      rw [Finset.length_toList]
      omega
    have hidx : j < c := hj.trans_le hlen
    have hf := hp ⟨j,hidx⟩
    simpa only [p, List.getElem?_eq_getElem hj, he, Option.map_some, Option.elim_some] using hf
  · rintro rfl j
    unfold p
    cases h : C.toList[j.val]? <;> simp [h]

theorem family_card (n c : ℕ) : Fintype.card (Pattern n c) = (1 + 2 * n) ^ c := by
  simp [Pattern, Nat.add_comm, Nat.mul_comm]

end PEqualNP.Outside.SparseCoordinateIsolation

theorem PEqualNP.Outside.SparseCoordinateIsolationFamily :
    ∀ n c : ℕ,
      Fintype.card (Fin c → Option (Fin n × Bool)) = (1 + 2 * n) ^ c ∧
      ∀ S : Finset (Fin n → Bool), S.card ≤ c + 1 →
        ∀ u ∈ S, ∃ p : Fin c → Option (Fin n × Bool),
          ∀ v ∈ S, (∀ i : Fin c, (p i).elim True (fun q => v q.1 = q.2)) ↔ v = u := by
  intro n c
  exact ⟨SparseCoordinateIsolation.family_card n c, SparseCoordinateIsolation.per_pattern⟩
