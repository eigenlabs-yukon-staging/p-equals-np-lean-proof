import PEqualNP.Outside.AffineHashIsolationBound

namespace PEqualNP.Outside.BoundedWordAffineIsolation

open PEqualNP.Outside.AffineHash

abbrev Word := List Bool

def embed (cap : ℕ) (w : Word) : Vec (2 * cap + 1) := fun j =>
  if j.val ≤ cap then (if j.val < w.length then 1 else 0)
  else (if w[j.val - (cap + 1)]?.getD false then 1 else 0)

theorem embed_injOn (cap : ℕ) :
    Set.InjOn (embed cap) ({w : Word | w.length ≤ cap} : Set Word) := by
  intro u hu v hv he
  change u.length ≤ cap at hu
  change v.length ≤ cap at hv
  have hlen : u.length = v.length := by
    rcases lt_trichotomy u.length v.length with h | h | h
    · have hj : u.length < 2 * cap + 1 := by omega
      have hb := congrFun he ⟨u.length, hj⟩
      simp [embed, hu, h] at hb
    · exact h
    · have hj : v.length < 2 * cap + 1 := by omega
      have hb := congrFun he ⟨v.length, hj⟩
      simp [embed, hv, h] at hb
  apply List.ext_getElem hlen
  intro i hiu hiv
  have hj : cap + 1 + i < 2 * cap + 1 := by omega
  have hb := congrFun he ⟨cap + 1 + i, hj⟩
  have hbefore : ¬ cap + 1 + i ≤ cap := by omega
  have hoffset : cap + 1 + i - (cap + 1) = i := by omega
  simp [embed, hbefore, hoffset, List.getElem?_eq_getElem, hiu, hiv] at hb
  split at hb <;> split at hb <;> simp_all

theorem only_iff (cap k : ℕ) (S : Finset Word)
    (hS : ∀ w ∈ S, w.length ≤ cap) (f : Seed (2 * cap + 1) k) :
    (∃ z ∈ S.image (embed cap), hit f z ∧ ∀ t ∈ S.image (embed cap), t ≠ z → ¬ hit f t) ↔
    (∃ w ∈ S, hit f (embed cap w) ∧ ∀ v ∈ S, v ≠ w → ¬ hit f (embed cap v)) := by
  constructor
  · rintro ⟨z, hz, hhit, huniq⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨w, hw, hhit, ?_⟩
    intro v hv hne
    apply huniq _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    exact fun h => hne (embed_injOn cap (hS v hv) (hS w hw) h)
  · rintro ⟨w, hw, hhit, huniq⟩
    refine ⟨embed cap w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, hhit, ?_⟩
    intro z hz hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact huniq v hv (fun h => hn (congrArg (embed cap) h))

end PEqualNP.Outside.BoundedWordAffineIsolation

open PEqualNP.Outside.AffineHash
open PEqualNP.Outside.BoundedWordAffineIsolation (embed embed_injOn only_iff)

theorem PEqualNP.Outside.BoundedWordAffineIsolation :
    ∀ cap : ℕ,
      ∃ E : List Bool → (Fin (2 * cap + 1) → ZMod 2),
        Set.InjOn E ({w : List Bool | w.length ≤ cap} : Set (List Bool)) ∧
        ∀ S : Finset (List Bool), S.Nonempty → (∀ w ∈ S, w.length ≤ cap) →
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 * cap + 3 ∧
            Fintype.card (Fin k → ((Fin (2 * cap + 1) → ZMod 2) × ZMod 2)) ≤ 8 *
              ((Finset.univ : Finset (Fin k → ((Fin (2 * cap + 1) → ZMod 2) × ZMod 2))).filter (fun f =>
                ∃ w ∈ S, (∀ i, (∑ j : Fin (2 * cap + 1), (f i).1 j * E w j) + (f i).2 = 0) ∧
                  ∀ v ∈ S, v ≠ w → ¬ (∀ i, (∑ j : Fin (2 * cap + 1), (f i).1 j * E v j) + (f i).2 = 0))).card := by
  intro cap
  refine ⟨embed cap, embed_injOn cap, ?_⟩
  intro S hS hsize
  let n : ℕ := 2 * cap + 1
  have hn : 0 < n := by omega
  have hne : (S.image (embed cap)).Nonempty := hS.image _
  obtain ⟨k, hk, hbound, hsmall, hlarge⟩ := width_exists (S.image (embed cap)) hne
  refine ⟨k, hk, by omega, ?_⟩
  have hboundCount := bound_at_width hn (S.image (embed cap)) hsmall hlarge
  let F : Finset (Seed n k) := Finset.univ
  have he : F.filter (fun f => ∃ z ∈ S.image (embed cap), hit f z ∧
      ∀ t ∈ S.image (embed cap), t ≠ z → ¬ hit f t) =
    F.filter (fun f => ∃ w ∈ S, hit f (embed cap w) ∧
      ∀ v ∈ S, v ≠ w → ¬ hit f (embed cap v)) := by
    ext f
    simp only [Finset.mem_filter]
    exact and_congr Iff.rfl (only_iff cap k S hsize f)
  change Fintype.card (Seed n k) ≤ 8 * _ at hboundCount ⊢
  rw [he] at hboundCount
  exact hboundCount
