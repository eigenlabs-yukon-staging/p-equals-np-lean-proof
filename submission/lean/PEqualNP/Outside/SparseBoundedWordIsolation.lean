import PEqualNP.Outside.SparseCoordinateIsolationFamily
import PEqualNP.Outside.UniformWitnessBitEncoding

namespace PEqualNP.Outside.SparseBoundedWordIsolation

open PEqualNP.Library.Universal
open PEqualNP.Outside.BoundedWordAffineIsolation (embed embed_injOn)
open PEqualNP.Outside.UniformWitnessBitEncoding (Word code code_bit field)
open PEqualNP.Outside.SparseCoordinateIsolation (Pattern permits per_pattern)

def bits (b : ℕ) (w : Word) (j : Fin (2 * b + 1)) : Bool :=
  ((code (un b) w)[j.val]?).getD false

private theorem field_bit_length (c w : Word) (hw : w.length ≤ c.length) (n : ℕ) (h : c.length = n)
    (j : Fin (2 * n + 1)) : field (((code c w)[j.val]?).getD false) = embed n w j := by
  subst n
  exact code_bit c w hw j

theorem bits_field (b : ℕ) (w : Word) (hw : w.length ≤ b) (j : Fin (2 * b + 1)) :
    field (bits b w j) = embed b w j :=
  field_bit_length (un b) w (by rwa [un_length]) b (un_length b) j

theorem bits_injOn (b : ℕ) :
    Set.InjOn (bits b) ({w : Word | w.length ≤ b} : Set Word) := by
  intro u hu v hv h
  refine embed_injOn b hu hv ?_
  funext i
  rw [← bits_field b u hu, ← bits_field b v hv, congrFun h i]

theorem isolated (b c : ℕ) (S : Finset Word) (hS : S.card ≤ c + 1)
    (hcap : ∀ w ∈ S, w.length ≤ b) (w : Word) (hw : w ∈ S) :
    ∃ p : Pattern (2 * b + 1) c, ∀ v ∈ S, permits p (bits b v) ↔ v = w := by
  classical
  have he : (S.image (bits b)).card = S.card :=
    Finset.card_image_of_injOn (fun u hu v hv h => bits_injOn b (hcap _ hu) (hcap _ hv) h)
  obtain ⟨p, hp⟩ := per_pattern (S.image (bits b)) (he.symm ▸ hS) (bits b w)
    (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  refine ⟨p, ?_⟩
  intro v hv
  exact (hp _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)).trans
    ⟨bits_injOn b (hcap _ hv) (hcap _ hw), congrArg (bits b)⟩

end PEqualNP.Outside.SparseBoundedWordIsolation

open PEqualNP.Outside.SparseBoundedWordIsolation

theorem PEqualNP.Outside.SparseBoundedWordIsolation :
    ∀ b c : ℕ, ∃ E : List Bool → (Fin (2 * b + 1) → Bool),
      Set.InjOn E ({w : List Bool | w.length ≤ b} : Set (List Bool)) ∧
      ∀ S : Finset (List Bool), S.card ≤ c + 1 → (∀ w ∈ S, w.length ≤ b) →
        ∀ w ∈ S, ∃ p : Fin c → Option (Fin (2 * b + 1) × Bool),
          ∀ v ∈ S, (∀ i : Fin c, (p i).elim True (fun q => E v q.1 = q.2)) ↔ v = w :=
  fun b c => ⟨bits b, bits_injOn b, fun S hS hcap w hw => isolated b c S hS hcap w hw⟩
